
(* $Id$ *)

open Names
open Generic

let lookup_var id =
  let rec look n = function
    | [] -> VAR id
    | (Name id')::_ when id = id' -> Rel n
    | _::r -> look (succ n) r
  in
  look 1

let rec globalize bv = function
  | VAR id -> lookup_var id bv
  | DOP1 (op,c) -> DOP1 (op, globalize bv c)
  | DOP2 (op,c1,c2) -> DOP2 (op, globalize bv c1, globalize bv c2)
  | DOPN (op,v) -> DOPN (op, Array.map (globalize bv) v)
  | DOPL (op,l) -> DOPL (op, List.map (globalize bv) l)
  | DLAM (na,c) -> DLAM (na, globalize (na::bv) c)
  | DLAMV (na,v) -> DLAMV (na, Array.map (globalize (na::bv)) v)
  | Rel _ | DOP0 _ as c -> c

let main () =
  let cs = Stream.of_channel stdin in
  while true do
    try
      let c = Grammar.Entry.parse G_minicoq.command cs in
      Printf.printf "ok\n"; flush stdout
    with 
      | End_of_file | Stdpp.Exc_located (_, End_of_file) -> 
	  exit 0
      | Stdpp.Exc_located (_,e) ->
	  Printf.printf "error: %s\n" (Printexc.to_string e); flush stdout
      | exn -> 
	  Printf.printf "error: %s\n" (Printexc.to_string exn); flush stdout
  done

let _ = Printexc.catch main ()

