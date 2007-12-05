(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Sign
open Declarations
open Inductive
open Type_errors
open Safe_typing
open G_minicoq

let (env : safe_environment ref) = ref empty_environment

let locals () =
  List.map (fun (id,b,t) -> (id, make_path [] id CCI))
    (named_context !env)

let lookup_named id =
  let rec look n = function
    | [] -> mkVar id
    | (Name id')::_ when id = id' -> mkRel n
    | _::r -> look (succ n) r
  in
  look 1

let args sign = Array.of_list (instance_from_section_context sign)

let rec globalize bv c = match kind_of_term c with
  | Var id -> lookup_named id bv
  | Const (sp, _) ->
      let cb = lookup_constant sp !env in mkConst (sp, args cb.const_hyps)
  | Ind (sp,_ as spi, _) ->
      let mib = lookup_mind sp !env in mkMutInd (spi, args mib.mind_hyps)
  | Construct ((sp,_),_ as spc, _) ->
      let mib = lookup_mind sp !env in mkMutConstruct (spc, args mib.mind_hyps)
  | _ -> map_constr_with_named_binders (fun na l -> na::l) globalize bv c

let check c = 
  let c = globalize [] c in
  let (j,u) = safe_infer !env c in
  let ty = j_type j in
  let pty = pr_term CCI (env_of_safe_env !env) ty in
  mSGNL (hov 0 (str"  :" ++ spc () ++ hov 0 pty ++ fnl ()))

let definition id ty c =
  let c = globalize [] c in
  let ty = Option.map (globalize []) ty in
  let ce = { const_entry_body = c; const_entry_type = ty } in
  let sp = make_path [] id CCI in
  env := add_constant sp ce (locals()) !env;
  mSGNL (hov 0 (pr_id id ++ spc () ++ str"is defined" ++ fnl ()))

let parameter id t =
  let t = globalize [] t in
  let sp = make_path [] id CCI in
  env := add_parameter sp t (locals()) !env;
  mSGNL (hov 0 (str"parameter" ++ spc () ++ pr_id id ++ 
		  spc () ++ str"is declared" ++ fnl ()))

let variable id t =
  let t = globalize [] t in
  env := push_named_assum (id,t) !env;
  mSGNL (hov 0 (str"variable" ++ spc () ++ pr_id id ++ 
		  spc () ++ str"is declared" ++ fnl ()))

let inductive par inds =
  let nparams = List.length par in
  let bvpar = List.rev (List.map (fun (id,_) -> Name id) par) in
  let name_inds = List.map (fun (id,_,_) -> Name id) inds in
  let bv = bvpar @  List.rev name_inds in
  let npar = List.map (fun (id,c) -> (Name id, globalize [] c)) par in
  let one_inductive (id,ar,cl) =
    let cv = List.map (fun (_,c) -> prod_it (globalize bv c) npar) cl in
    { mind_entry_nparams = nparams;
      mind_entry_params = List.map (fun (id,c) -> (id, LocalAssum c)) par;
      mind_entry_typename = id;
      mind_entry_arity = prod_it (globalize bvpar ar) npar;
      mind_entry_consnames = List.map fst cl;
      mind_entry_lc = cv }
  in
  let inds = List.map one_inductive inds in
  let mie = { 
    mind_entry_finite = true;
    mind_entry_inds = inds }
  in
  let sp =
    let mi1 = List.hd inds in
    make_path [] mi1.mind_entry_typename CCI in
  env := add_mind sp mie (locals()) !env;
  mSGNL (hov 0 (str"inductive type(s) are declared" ++ fnl ()))


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
      mSGNL (hov 0 (str "type error:" ++ spc () ++ 
		      Explain.explain_type_error k ctx te ++ fnl ()))
  | Stdpp.Exc_located (_,exn) -> 
      explain_exn exn
  | exn -> 
      mSGNL (hov 0 (str"error: " ++ str (Printexc.to_string exn) ++ fnl ()))

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

