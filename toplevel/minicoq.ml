
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
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

let inductive par inds =
  let nparams = List.length par in
  let bvpar = List.rev (List.map (fun (id,_) -> Name id) par) in
  let name_inds = List.map (fun (id,_,_) -> Name id) inds in
  let bv = bvpar @  List.rev name_inds in
  let par = List.map (fun (id,c) -> (Name id, globalize [] c)) par in
  let one_inductive (id,ar,cl) =
    let cv = Array.of_list (List.map snd cl) in
    let cv = Array.map (fun c -> prod_it (globalize bv c) par) cv in
    let c = put_DLAMSV name_inds cv in
    (id, prod_it (globalize bvpar ar) par, List.map fst cl, c)
  in
  let inds = List.map one_inductive inds in
  let mie = { 
    mind_entry_nparams = nparams;
    mind_entry_finite = true;
    mind_entry_inds = inds }
  in
  let sp = let (id,_,_,_) = List.hd inds in make_path [] id CCI in
  env := add_mind sp mie !env;
  mSGNL (hOV 0 [< 'sTR"inductive type(s) are declared"; 'fNL >])


let execute = function
  | Check c -> check c
  | Definition (id, ty, c) -> definition id ty c
  | Parameter (id, t) -> parameter id t
  | Variable (id, t) -> variable id t
  | Inductive (par,inds) -> inductive par inds

let parse_file f =
  let c = open_in f in
  let cs = Stream.of_channel c in
  try
    while true do
      let c = Grammar.Entry.parse command cs in execute c
    done
  with 
    | End_of_file | Stdpp.Exc_located (_, End_of_file) -> close_in c; exit 0
    | exn -> close_in c; raise exn
      
let top () =
  let cs = Stream.of_channel stdin in
  while true do
    try
      let c = Grammar.Entry.parse command cs in execute c
    with 
      | End_of_file | Stdpp.Exc_located (_, End_of_file) -> 
	  exit 0
      | Stdpp.Exc_located (_,exn) ->
	  mSGNL [< 'sTR"error: "; 'sTR (Printexc.to_string exn); 'fNL >]
      | exn -> 
	  mSGNL [< 'sTR"error: "; 'sTR (Printexc.to_string exn); 'fNL >]
  done

let main () =
  if Array.length Sys.argv = 1 then
    parse_file "test"
  else
    if Sys.argv.(1) = "-top" then top () else parse_file (Sys.argv.(1))

let _ = Printexc.print main ()

