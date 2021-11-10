(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Termops
open EConstr

module NamedDecl = Context.Named.Declaration

(* tactical to save as name a subproof such that the generalisation of
   the current goal, abstracted with respect to the local signature,
   is solved by tac *)

(** d1 is the section variable in the global context, d2 in the goal context *)
let interpretable_as_section_decl env sigma d1 d2 =
  let open Context.Named.Declaration in
  let e_eq_constr_univs sigma c1 c2 = match eq_constr_universes env sigma c1 c2 with
    | None -> false
    | Some cstr ->
      try
        let _sigma = Evd.add_universe_constraints sigma cstr in
        true
      with UState.UniversesDiffer -> false
  in
  match d2, d1 with
  | LocalDef _, LocalAssum _ -> false
  | LocalDef (_,b1,t1), LocalDef (_,b2,t2) ->
    e_eq_constr_univs sigma b1 b2 && e_eq_constr_univs sigma t1 t2
  | LocalAssum (_,t1), d2 -> e_eq_constr_univs sigma t1 (NamedDecl.get_type d2)

let name_op_to_name ~name_op ~name suffix =
  match name_op with
  | Some s -> s
  | None -> Nameops.add_suffix name suffix

let declare_abstract = ref (fun ~name ~poly ~kind ~sign ~secsign ~opaque ~solve_tac sigma concl ->
  CErrors.anomaly (Pp.str "Abstract declaration hook not registered"))

let cache_term_by_tactic_then ~opaque ~name_op ?(goal_type=None) tac tacK =
  let open Tacticals in
  let open Tacmach in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (name, poly) ->
  (* This is important: The [Global] and [Proof Theorem] parts of the
     goal_kind are not relevant here as build_constant_by_tactic does
     use the noop terminator; but beware if some day we remove the
     redundancy on constant declaration. This opens up an interesting
     question, how does abstract behave when discharge is local for example?
  *)
  let suffix, kind = if opaque
    then "_subproof", Decls.(IsProof Lemma)
    else "_subterm", Decls.(IsDefinition Definition)
  in
  let name = name_op_to_name ~name_op ~name suffix in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let section_sign = Global.named_context_val () in
    let goal_sign = Proofview.Goal.hyps gl in
    let sign,secsign =
      List.fold_right
        (fun d (s1,s2) ->
           let id = NamedDecl.get_id d in
           if mem_named_context_val id section_sign &&
              interpretable_as_section_decl env sigma (lookup_named_val id section_sign) d
           then (s1,push_named_context_val d s2)
           else (Context.Named.add d s1,s2))
        goal_sign (Context.Named.empty, Environ.empty_named_context_val)
    in
    let name = Namegen.next_global_ident_away name (pf_ids_set_of_hyps gl) in
    let concl = match goal_type with
      | None ->  Proofview.Goal.concl gl
      | Some ty -> ty
    in
    let concl = it_mkNamedProd_or_LetIn concl sign in
    let solve_tac = tclCOMPLETE
        (Tactics.intros_mustbe_force (List.rev_map NamedDecl.get_id sign) <*>
         tac)
    in
    let effs, sigma, lem, args, safe =
      !declare_abstract ~name ~poly ~sign ~secsign ~kind ~opaque ~solve_tac sigma concl
    in
    let solve =
      Proofview.tclEFFECTS effs <*>
      tacK lem args
    in
    let tac = if not safe then Proofview.mark_as_unsafe <*> solve else solve in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac
  end

let abstract_subproof ~opaque tac =
  cache_term_by_tactic_then ~opaque tac (fun lem args -> Tactics.exact_no_check (applist (lem, args)))

let tclABSTRACT ?(opaque=true) name_op tac =
  abstract_subproof ~opaque ~name_op tac
