#require "podge"

let () = 
  Podge.Unix.read_lines "code.ml" |> List.iter print_endline

let () = 
  Podge.Unix.read_process_output "ls -halt" |> List.iter print_endline
