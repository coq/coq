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
open Context
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
  let evm = evars_of !isevars in    
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

let coqintern evd env : Topconstr.constr_expr -> Rawterm.rawconstr = Constrintern.intern_constr (evars_of evd) env
let coqinterp evd env : Topconstr.constr_expr -> Term.constr = Constrintern.interp_constr (evars_of evd) env

let env_with_binders env isevars l =
  let rec aux ((env, rels) as acc) = function
      Topconstr.LocalRawDef ((loc, name), def) :: tl -> 
	let rawdef = coqintern !isevars env def in
	let coqdef, deftyp = interp env isevars rawdef empty_tycon in
	let reldecl = (name, Some coqdef, deftyp) in
	  aux  (push_rel reldecl env, reldecl :: rels) tl
    | Topconstr.LocalRawAssum (bl, typ) :: tl ->
	let rawtyp = coqintern !isevars env typ in
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

let subtac_process env isevars id l c tycon =
  let evars () = evars_of !isevars in
  let _ = trace (str "Creating env with binders") in
  let env_binders, binders_rel = env_with_binders env isevars l in
  let _ = trace (str "New env created:" ++ my_print_context env_binders) in
  let tycon = 
    match tycon with
	None -> empty_tycon
      | Some t -> 
	  let t = coqintern !isevars env_binders t in
	  let _ = trace (str "Internalized specification: " ++ my_print_rawconstr env_binders t) in
	  let coqt, ttyp = interp env_binders isevars t empty_tycon in
	  let _ = trace (str "Interpreted type: " ++ my_print_constr env_binders coqt) in
	    mk_tycon coqt
  in    
  let c = coqintern !isevars env_binders c in
  let c = Subtac_utils.rewrite_cases env c in
  let _ = trace (str "Internalized term: " ++ my_print_rawconstr env c) in
  let coqc, ctyp = interp env_binders isevars c tycon in
  let _ = trace (str "Interpreted term: " ++ my_print_constr env_binders coqc ++ spc () ++
		 str "Coq type: " ++ my_print_constr env_binders ctyp)
  in
  let _ = trace (str "Original evar map: " ++ Evd.pr_evar_map (evars ())) in
    
  let fullcoqc = it_mkLambda_or_LetIn coqc binders_rel 
  and fullctyp = it_mkProd_or_LetIn ctyp binders_rel
  in
  let fullcoqc = Evarutil.nf_evar (evars_of !isevars) fullcoqc in
  let fullctyp = Evarutil.nf_evar (evars_of !isevars) fullctyp in

  let _ = trace (str "After evar normalization: " ++ spc () ++
		 str "Coq term: " ++ my_print_constr env fullcoqc ++ spc ()
		 ++ str "Coq type: " ++ my_print_constr env fullctyp) 
  in
  let evm = non_instanciated_map env isevars in
  let _ = trace (str "Non instanciated evars map: " ++ Evd.pr_evar_map evm) in
    evm, fullcoqc, fullctyp
