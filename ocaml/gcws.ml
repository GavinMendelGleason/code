(* Attempt to make gcws more efficient *) 

open String;;
open List;; 
open Str;;

module StringMap = Map.Make (String);; 

type window = { base : string; start_index : int; end_index : int };;
type view = Window of window | Empty;;
type version = int;;
type versions = version list;;
type maxcount = int;;
type suffixtree = Nulltree 
				  | View of view * version
				  | Suffixtree of 
					  (suffixtree * versions * maxcount) StringMap.t;;

(* peel to nearest whitespace *)
let peel view = 
  let rec peel_aux view count = 
	match view with
		Empty -> (Empty,Empty)
	  | Window window -> 
		  if (count = window.end_index - window.start_index) then
			if count == 0 then 
			  (Empty,Empty)
			else
			  ( Window { base = window.base; 
						 start_index = window.start_index; 
						 end_index = window.end_index }, 
				Empty ) 
		  else if (get window.base (window.start_index + count) = ' ') 
		  then
			if (window.start_index+count+1 = window.end_index) then 
			  ( Window { base = window.base; 
						 start_index = window.start_index; 
						 end_index = window.start_index + count }, 
				Empty)
			else
			  ( Window { base = window.base; 
						 start_index = window.start_index; 
						 end_index = window.start_index + count }, 
				Window { base = window.base; 
						 start_index = window.start_index + count + 1; 
						 end_index = window.end_index } )
		  else 
			peel_aux view (count+1)
  in
	peel_aux view 0;;

let string2view str = 
  Window { base = str; start_index = 0; end_index = (String.length str)};;

let view2string view = 
  match view with 
	  Empty -> ""
	| Window window -> 
		sub window.base 
		  window.start_index 
		  (window.end_index - window.start_index);;

let rec render_suffixtree st = 
  match st with
	  Nulltree -> "" 
	| View (v,ver) -> ("{"^(view2string v)^"}\n")
	| Suffixtree map -> 
		StringMap.fold 
		  (fun key tup level ->
			 let (st,vl,_) = tup in
			   (level^".."^key^":"^(List.fold_right (fun x l -> l^(string_of_int x)) vl "")^"=>"^(render_suffixtree st)))
		  map "";;

let print_suffixtree st = 
  print_string (render_suffixtree st);;

let rec add_view2suffixtree view suffixtree version = 
  (* print_string ("view: "^(view2string view)^"\n");*)
  match view with 
	  Empty -> (suffixtree,0)
	| Window _ -> 
		match suffixtree with 
			Nulltree -> 
			  ((View (view,version)),0)
		  |	View (old_view,old_version) -> 
			  (* split, leave the old key and recurse *)
			  let (oh,ot) = peel old_view in
			  let old_str = view2string oh in 
			  let map = StringMap.add old_str (View (ot,old_version),[old_version],0) StringMap.empty in
				add_view2suffixtree view (Suffixtree map) version
		  | Suffixtree map -> 
			  let (h,t) = peel view in
			  let str = view2string h in
				(* recurse on the split *)
				if StringMap.mem str map then
				  let (suffixtree,versions,maxcount) = (StringMap.find str map) in
				  let (new_tree,submax) = (add_view2suffixtree t suffixtree version) in
					if (List.mem version versions) then
					  let map = StringMap.add str (new_tree, versions, maxcount) map in
						(Suffixtree map, maxcount)
					else
					  let map = StringMap.add str (new_tree, version::versions, (max maxcount submax)) map in
						(Suffixtree map, (max (maxcount+String.length str) (submax+String.length str)))
				else
				  let map = StringMap.add str (View (t,version),[version],0) map in
                    (Suffixtree map, 0);;

let rec add_suffixes view suffixtree version = 
  match view with 
	  Empty -> suffixtree
	| _ -> 
		let (st,_) = add_view2suffixtree view suffixtree version in
		let (h,t) = peel view in
		  add_suffixes t st version;;

let rec greatest_sequence suffixtree = 
  match suffixtree with 
	  Nulltree -> 
		[]
	| View (view,version) -> 
		[]
	| Suffixtree map -> 
		let (maximum,key) = StringMap.fold (fun key tup maxkey ->
											  let (_,_,value) = tup in
											  let (old_max,old_key) = maxkey in 
												if value < old_max then
												  (old_max,old_key)
												else 
												  (value,key)) map (0,"")
		in
		let (subtree,versions,maxcount) = StringMap.find key map
		in
		  (* if there is only one version, then it can't be common *)
		  match versions with 
			  h::[] -> []
			| _ -> 
				key :: (greatest_sequence subtree);;

let stringlist2suffixtree stringlist = 
  let (st,_) = 
	List.fold_right 
	  (fun string st_version -> 
		 let (st,version) = st_version in
		 let new_version = version+1 in
		   (add_suffixes (string2view string) st new_version,
			new_version))
	  stringlist
	  (Nulltree,0) in
	st;;


let main () =
  let rec get_strings () = 
	let string = (try 
					read_line ()
				  with End_of_file -> "") in
	  if string = "" then
		[]
	  else
		let string = String.lowercase string in
		let ent_pat = Str.regexp "&\\(#x[0-9A-Fa-f]+\\|#[0-9]+\\|[A-Za-z]+\\);" in
		let string = Str.global_replace ent_pat " " string in
		let punc_pat = Str.regexp "[^A-Za-z]" in 
		let string = Str.global_replace punc_pat " " string in 
		let space_pat = Str.regexp "[ ]+" in 
		let string = Str.global_replace space_pat " " string in
 		  string :: get_strings ()
  in
  let st = stringlist2suffixtree (get_strings ()) in
  let word_list = greatest_sequence st in
	print_string ((String.concat " " word_list)^"\n") 
	;
	exit 0 ;;

main ();;
