
open Printf

let file = Sys.argv.(1)

let cin = open_in file
let cout = open_out (file ^ ".v8")

let (coq_out, coq_in) as chan = Unix.open_process "coqtop -translate"

let begin_coq = 
  Str.regexp 
    "\\\\begin{coq_\\(example\\|example\\*\\|example\\#\\|eval\\)}[ \t]*$"

let end_coq = 
  Str.regexp 
    "\\\\end{coq_\\(example\\|example\\*\\|example\\#\\|eval\\)}[ \t]*$"

let new_syntax =
  Str.regexp "New Syntax:[ \t]*$"

(* on envoie un Check O et on saute les 2 premiers New Syntax *)
let _ =
  output_string coq_in "Check O.\n";
  flush coq_in;
  while not (Str.string_match new_syntax (input_line coq_out) 0) do () done;
  while not (Str.string_match new_syntax (input_line coq_out) 0) do () done;
  printf "** init terminée\n"; flush stdout

let iter_char_until_dot cin f =
  printf "** entrée dans iter_char\n"; flush stdout;
  let last_c = ref ' ' in
  let rec loop () =
    let c = input_char cin in
    printf "[%c]" c; flush stdout;
    f c;
    if !last_c = '.' && (c = ' ' || c = '\t' || c = '\n') then 
      () 
    else begin
      last_c := c;
      loop ()
    end
  in
  loop ()
    
let trad_commands () =
  (* on copie toutes les commandes dans un fichier temporaire *)
  let tmp = Filename.temp_file "trad" ".v" in
  let tmp_in, end_s = 
    let tmp_out = open_out tmp in
    let rec loop () =
      let s = input_line cin in
      if Str.string_match end_coq s 0 then begin
	close_out tmp_out;
	open_in tmp, s
      end else begin
	output_string tmp_out (s ^ "\n");
	loop ()
      end
    in
    loop ()
  in
  ignore (Sys.command (Printf.sprintf "cat %s" tmp));
  let one_command () =
    (* on envoie toute la commande a Coq *)
    iter_char_until_dot tmp_in (fun c -> output_char coq_in c);
    (* on flush *)
    flush coq_in;
    (* on lit la réponse *)
    try
      (* 1. on cherche la ligne "New Syntax:" *)
      while true do 
	let s = input_line coq_out in
	if Str.string_match new_syntax s 0 then raise Exit
      done
    with Exit ->
      (* 2. on copie tout jusqu'au point *)
      printf "** New Syntax trouvé\n"; flush stdout;
      iter_char_until_dot coq_out (fun c -> output_char cout c);
      printf "** copie terminée\n"; flush stdout;
      flush cout
  in    
  try
    while true do one_command () done; assert false
  with End_of_file ->
    printf "** End_of_file\n"; flush stdout;
    Sys.remove tmp;
    end_s

let trad () =
  while true do
    let s = input_line cin in
    output_string cout (s ^ "\n");
    if Str.string_match begin_coq s 0 then 
      let s = trad_commands () in
      output_string cout (s ^ "\n");
  done

let _ =
  try 
    trad () 
  with End_of_file -> 
    close_out cout; 
    printf "** close_out cout\n"; flush stdout;
    ignore (Unix.close_process chan)
