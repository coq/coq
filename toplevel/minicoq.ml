
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
open Term
open Sign
open Declarations
open Inductive
open Type_errors
open Safe_typing
open G_minicoq

let (env : safe_environment ref) = ref empty_environment

let lookup_var id =
  let rec look n = function
    | [] -> VAR id
    | (Name id')::_ when id = id' -> Rel n
    | _::r -> look (succ n) r
  in
  look 1

let args sign = 
  Array.of_list (List.map (fun id -> VAR id) (ids_of_var_context sign))

let rec globalize bv c = match kind_of_term c with
  | IsVar id -> lookup_var id bv
  | IsConst (sp, _) ->
      let cb = lookup_constant sp !env in mkConst (sp, args cb.const_hyps)
  | IsMutInd (sp,_ as spi, _) ->
      let mib = lookup_mind sp !env in mkMutInd (spi, args mib.mind_hyps)
  | IsMutConstruct ((sp,_),_ as spc, _) ->
      let mib = lookup_mind sp !env in mkMutConstruct (spc, args mib.mind_hyps)
  | _ -> map_constr_with_binders (fun na l -> na::l) globalize bv c

(*
let rec globalize bv = function
  | VAR id -> lookup_var id bv
  | DOP1 (op,c) -> DOP1 (op, globalize bv c)
  | DOP2 (op,c1,c2) -> DOP2 (op, globalize bv c1, globalize bv c2)
  | DOPN (Const sp as op, _) ->
      let cb = lookup_constant sp !env in DOPN (op, args cb.const_hyps)
  | DOPN (MutInd (sp,_) as op, _) ->
      let mib = lookup_mind sp !env in DOPN (op, args mib.mind_hyps)
  | DOPN (MutConstruct ((sp,_),_) as op, _) ->
      let mib = lookup_mind sp !env in DOPN (op, args mib.mind_hyps)
  | DOPN (op,v) -> DOPN (op, Array.map (globalize bv) v)
  | DLAM (na,c) -> DLAM (na, globalize (na::bv) c)
  | DLAMV (na,v) -> DLAMV (na, Array.map (globalize (na::bv)) v)
  | CLam(n,t,c)   -> CLam (n, globalize bv t, globalize (n::bv) c)  
  | CPrd(n,t,c)   -> CPrd (n, globalize bv t, globalize (n::bv) c)
  | CLet(n,b,t,c) -> CLet (n,globalize bv b,globalize bv t,globalize (n::bv) c)
  | Rel _ | DOP0 _ as c -> c
*)

let check c = 
  let c = globalize [] c in
  let (j,u) = safe_infer !env c in
  let ty = j_type j in
  let pty = pr_term CCI (env_of_safe_env !env) ty in
  mSGNL (hOV 0 [< 'sTR"  :"; 'sPC; hOV 0 pty; 'fNL >])

let definition id ty c =
  let c = globalize [] c in
  let ty = option_app (globalize []) ty in
  let ce = { const_entry_body = Cooked c; const_entry_type = ty } in
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
  env := push_var_decl (id,t) !env;
  mSGNL (hOV 0 [< 'sTR"variable"; 'sPC; print_id id; 
		  'sPC; 'sTR"is declared"; 'fNL >])

let put_DLAMSV lna lc = 
  match lna with 
    | [] -> anomaly "put_DLAM"
    | na::lrest -> List.fold_left (fun c na -> DLAM(na,c)) (DLAMV(na,lc)) lrest

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
    (id, prod_it (globalize bvpar ar) par, List.map fst cl, [c])
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

module Explain = Fhimsg.Make(struct let pr_term = pr_term end)

let rec explain_exn = function
  | TypeError (k,ctx,te) -> 
      mSGNL (hOV 0 [< 'sTR "type error:"; 'sPC; 
		      Explain.explain_type_error k ctx te; 'fNL >])
  | Stdpp.Exc_located (_,exn) -> 
      explain_exn exn
  | exn -> 
      mSGNL (hOV 0 [< 'sTR"error: "; 'sTR (Printexc.to_string exn); 'fNL >])

let top () =
  let cs = Stream.of_channel stdin in
  while true do
    try
      let c = Grammar.Entry.parse command cs in execute c
    with 
      | End_of_file | Stdpp.Exc_located (_, End_of_file) -> exit 0
      | exn -> explain_exn exn
  done

let main () =
  if Array.length Sys.argv = 1 then
    parse_file "test"
  else
    if Sys.argv.(1) = "-top" then top () else parse_file (Sys.argv.(1))

let _ = Printexc.print main ()

