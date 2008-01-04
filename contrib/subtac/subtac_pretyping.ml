(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Global
open Pp
open Util
open Names
open Sign
open Evd
open Term
open Termops
open Reductionops
open Environ
open Type_errors
open Typeops
open Libnames
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Pattern
open Dyn

open Subtac_coercion
open Subtac_utils
open Coqlib
open Printer
open Subtac_errors
open Eterm

module Pretyping = Subtac_pretyping_F.SubtacPretyping_F(Subtac_coercion.Coercion)

open Pretyping

let _ = Pretyping.allow_anonymous_refs := true

type recursion_info = {
  arg_name: name;
  arg_type: types; (* A *)
  args_after : rel_context;
  wf_relation: constr; (* R : A -> A -> Prop *)
  wf_proof: constr; (* : well_founded R *)
  f_type: types; (* f: A -> Set *)
  f_fulltype: types; (* Type with argument and wf proof product first *)
}

let my_print_rec_info env t = 
  str "Name: " ++ Nameops.pr_name t.arg_name ++ spc () ++
  str "Arg type: " ++ my_print_constr env t.arg_type ++ spc () ++
  str "Wf relation: " ++ my_print_constr env t.wf_relation ++ spc () ++
  str "Wf proof: " ++ my_print_constr env t.wf_proof ++ spc () ++
  str "Abbreviated Type: " ++ my_print_constr env t.f_type ++ spc () ++
  str "Full type: " ++ my_print_constr env t.f_fulltype
(*   trace (str "pretype for " ++ (my_print_rawconstr env c) ++ *)
(* 	   str " and tycon "++ my_print_tycon env tycon ++ *)
(* 	   str " in environment: " ++ my_print_env env); *)

let merge_evms x y = 
  Evd.fold (fun ev evi evm -> Evd.add evm ev evi) x y

let interp env isevars c tycon = 
  let j = pretype tycon env isevars ([],[]) c in
  let _ = isevars := Evarutil.nf_evar_defs !isevars in
  let evd,_ = consider_remaining_unif_problems env !isevars in
  let unevd = undefined_evars evd in
  let unevd' = Typeclasses.resolve_typeclasses env (Evd.evars_of unevd) evd in
  let evm = evars_of unevd' in
    isevars := unevd';
    nf_evar evm j.uj_val, nf_evar evm j.uj_type

let find_with_index x l =
  let rec aux i = function
      (y, _, _) as t :: tl -> if x = y then i, t else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

let list_split_at index l = 
  let rec aux i acc = function
      hd :: tl when i = index -> (List.rev acc), tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "list_split_at: Invalid argument"
  in aux 0 [] l

open Vernacexpr

let coqintern_constr evd env : Topconstr.constr_expr -> Rawterm.rawconstr = Constrintern.intern_constr (evars_of evd) env
let coqintern_type evd env : Topconstr.constr_expr -> Rawterm.rawconstr = Constrintern.intern_type (evars_of evd) env

let env_with_binders env isevars l =
  let rec aux ((env, rels) as acc) = function
      Topconstr.LocalRawDef ((loc, name), def) :: tl -> 
	let rawdef = coqintern_constr !isevars env def in
	let coqdef, deftyp = interp env isevars rawdef empty_tycon in
	let reldecl = (name, Some coqdef, deftyp) in
	  aux  (push_rel reldecl env, reldecl :: rels) tl
    | Topconstr.LocalRawAssum (bl, k, typ) :: tl ->
	let rawtyp = coqintern_type !isevars env typ in
	let coqtyp, typtyp = interp env isevars rawtyp empty_tycon in
	let acc = 
	  List.fold_left (fun (env, rels) (loc, name) -> 
			    let reldecl = (name, None, coqtyp) in
			      (push_rel reldecl env, 
			       reldecl :: rels))
	    (env, rels) bl
	in aux acc tl
    | [] -> acc
  in aux (env, []) l

let subtac_process env isevars id bl c tycon =
(*   let bl = Implicit_quantifiers.ctx_of_class_binders (vars_of_env env) cbl @ l in *)
  let c = Command.abstract_constr_expr c bl in
  let tycon = 
    match tycon with
	None -> empty_tycon
      | Some t -> 
	  let t = Command.generalize_constr_expr t bl in
	  let t = coqintern_type !isevars env t in
	  let coqt, ttyp = interp env isevars t empty_tycon in
	    mk_tycon coqt
  in    
  let c = coqintern_constr !isevars env c in
  let imps = Implicit_quantifiers.implicits_of_rawterm c in
  let coqc, ctyp = interp env isevars c tycon in
  let evm = non_instanciated_map env isevars (evars_of !isevars) in
    evm, coqc, ctyp, imps

open Subtac_obligations

let subtac_proof env isevars id bl c tycon =
  let evm, coqc, coqt, imps = subtac_process env isevars id bl c tycon in
  let evm = Subtac_utils.evars_of_term evm Evd.empty coqc in
  let evars, def, ty = Eterm.eterm_obligations env id !isevars evm 0 coqc coqt in
    add_definition id def ty ~implicits:imps evars
