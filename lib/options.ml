
(* $Id$ *)

let batch_mode = ref false

let debug = ref false

let print_emacs = ref false

let emacs_str s = if !print_emacs then s else "" 

(* Silent *)
let silent = ref false
let make_silent flag = silent := flag; ()
let is_silent () = !silent

let silently f x =
  let oldsilent = !silent in
  try 
    silent := true;
    let rslt = f x in
    silent := oldsilent; 
    rslt
  with e -> begin
    silent := oldsilent; raise e
  end
