
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Constant
open Inductive
open Typing
open G_minicoq

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

let (env : unit environment ref) = ref empty_environment

let check c = 
  let c = globalize [] c in
  let (j,u) = safe_machine !env c in
  mSGNL (hOV 0 [< 'sTR"  :"; 'sPC; hOV 0 (pr_term (j_type j)); 'fNL >])

let definition id ty c =
  let c = globalize [] c in
  let ty = option_app (globalize []) ty in
  let ce = { const_entry_body = c; const_entry_type = ty } in
  let sp = make_path [] id CCI in
  env := add_constant sp ce !env;
  mSGNL (hOV 0 [< print_id id; 'sPC; 'sTR"is defined"; 'fNL >])

let parameter id t =
  let t = globalize [] t in
  let sp = make_path [] id CCI in
  env := add_parameter sp t !env;
  mSGNL (hOV 0 [< 'sTR"parameter"; 'sPC; print_id id; 
		  'sPC; 'sTR"is declared"; 'fNL >])

let variable id t =
  let t = globalize [] t in
  env := push_var (id,t) !env;
  mSGNL (hOV 0 [< 'sTR"variable"; 'sPC; print_id id; 
		  'sPC; 'sTR"is declared"; 'fNL >])

let execute = function
  | Check c -> check c
  | Definition (id, ty, c) -> definition id ty c
  | Parameter (id, t) -> parameter id t
  | Variable (id, t) -> variable id t
  | _ -> Printf.printf "not yet implemented\n"; flush stdout

let main () =
  let cs = Stream.of_channel stdin in
  while true do
    try
      let c = Grammar.Entry.parse command cs in
      execute c
    with 
      | End_of_file | Stdpp.Exc_located (_, End_of_file) -> 
	  exit 0
      | Stdpp.Exc_located (_,exn) ->
	  mSGNL [< 'sTR"error: "; 'sTR (Printexc.to_string exn); 'fNL >]
      | exn -> 
	  mSGNL [< 'sTR"error: "; 'sTR (Printexc.to_string exn); 'fNL >]
  done

let _ = Printexc.catch main ()

