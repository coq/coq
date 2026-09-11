(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open EConstr

module NamedDecl = Context.Named.Declaration

(* tactical to save as name a subproof such that the generalisation of
   the current goal, abstracted with respect to the local signature,
   is solved by tac *)

let name_op_to_name ~name_op ~name suffix =
  match name_op with
  | Some s -> s
  | None -> Nameops.add_suffix name suffix

let cache_term_by_tactic_then ~opaque ~name_op ?(goal_type=None) tac tacK =
  let open Tacticals in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (name, poly) ->
  let suffix = if opaque then "_subproof" else "_subterm" in
  let name = name_op_to_name ~name_op ~name suffix in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    (* XXX we cannot use [tclENV] here because toplevel callers may pass wrong
       named contexts when nesting abstracts. See #5641. *)
    let section_sign = Global.named_context_val () in
    let goal_sign = Proofview.Goal.hyps gl in
    let sign,secsign =
      List.fold_right
        (fun d (s1,s2) ->
           match Environ.var_status (NamedDecl.get_id d) env with
           | SecVar -> (s1,push_named_context_val SecVar d s2)
           | ProofVar -> (Context.Named.add d s1,s2))
        goal_sign (Context.Named.empty, Environ.empty_named_context_val)
    in
    let bad id = match lookup_named_val id section_sign with
    | (_ : named_declaration) -> true
    | exception Not_found ->
      Evd.seff_mem_label id (Evd.eval_side_effects sigma) ||
      (* The local environment is OK when it comes to constants though,
         including those defined by [tclABSTRACT]. *)
      let kn = Lib.make_kn id in
      let kn = Names.Constant.make1 kn in
      Environ.mem_constant kn env
    in
    let name = Namegen.next_ident_away_from name bad in
    let concl = match goal_type with
      | None ->  Proofview.Goal.concl gl
      | Some ty -> ty
    in
    let concl = it_mkNamedProd_or_LetIn sigma concl sign in
    let solve_tac = tclCOMPLETE
        (Tactics.intros_mustbe_force (List.rev_map NamedDecl.get_id sign) <*>
         tac)
    in
    let sigma, lem, args, safe =
      Subproof.declare_abstract ~name ~poly ~sign ~secsign ~opaque ~solve_tac env sigma concl
    in
    let pose_tac = match name_op with
    | None -> Proofview.tclUNIT ()
    | Some id ->
      if opaque then Tactics.pose_proof (Names.Name id) lem
      else Tactics.pose_tac (Names.Name id) lem
    in
    let mark = if not safe then Proofview.mark_as_unsafe else tclIDTAC in
    tclTHENLIST [
      Proofview.Unsafe.tclEVARS sigma;
      mark;
      pose_tac;
      tacK lem args;
    ];
  end

let abstract_subproof ~opaque tac =
  cache_term_by_tactic_then ~opaque tac (fun lem args -> Tactics.exact_no_check (applist (lem, args)))

let tclABSTRACT ?(opaque=true) name_op tac =
  abstract_subproof ~opaque ~name_op tac

let { Goptions.get = get_inline_abstract_subproof } =
  Goptions.declare_bool_option_and_ref
    ~depr:(Deprecation.make ~since:"9.3" ())
    ~key:["Inline"; "Abstract"; "Subproof"]
    ~value:false
    ()

let () = Hook.set Proof.abstract_hook
    (fun tac -> tclABSTRACT None tac)
