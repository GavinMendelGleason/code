
module Set = struct
  let empty = []
  let add x l = x :: l
  let mem x l = List.mem x l
end;;

let rec unique alread_read =
  output_string stdout "> ";
  flush stdout;
  let line = input_line stdin in
  if not (Set.mem line already_read)
  then
    begin
      output_string stdout line;
      output_char stdout '\n';
      unique (Set.add line already_read)
    end
  else
    unique already_read;;

try unique Set.empty with
  End_of_file -> ();;

