(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Context.Named.Declaration
open Vernacentries.DefAttributes

(** [start_deriving f suchthat lemma] starts a proof of [suchthat]
    (which can contain references to [f]) in the context extended by
    [f:=?x]. When the proof ends, [f] is defined as the value of [?x]
    and [lemma] as the proof. *)
let start_deriving ~atts CAst.{v=f;loc} suchthat name : Declare.Proof.t =

  let scope, _local, poly, program_mode, user_warns, typing_flags, using, clearbody =
    atts.scope, atts.locality, atts.polymorphic, atts.program, atts.user_warns, atts.typing_flags, atts.using, atts.clearbody in
  if program_mode then CErrors.user_err (Pp.str "Program mode not supported.");

  let env = Global.env () in
  let sigma = Evd.from_env env in
  let kind = Decls.(IsDefinition Definition) in

  (* create a sort variable for the type of [f] *)
  (* spiwack: I don't know what the rigidity flag does, picked the one
     that looked the most general. *)
  let sigma, (f_type, f_impargs) =
    let (sigma,f_type_sort) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
    let f_type_type = EConstr.mkSort f_type_sort in
    let sigma, f_type = Evarutil.new_evar env sigma ~src:(Loc.tag @@ Evar_kinds.GoalEvar) ~typeclass_candidate:false f_type_type in
    let sigma = Evd.shelve sigma [fst (EConstr.destEvar sigma f_type)] in
    sigma, (f_type, [])
  in
  let (sigma, ef) = Evarutil.new_evar env sigma ~src:(Loc.tag @@ Evar_kinds.GoalEvar) ~typeclass_candidate:false f_type in
  let env' = EConstr.push_named (LocalDef (EConstr.annotR f, ef, f_type)) env in
  let impls = Names.Id.Map.add f (Constrintern.compute_internalization_data env sigma f Constrintern.Variable f_type f_impargs) Constrintern.empty_internalization_env in
  let sigma = Evd.shelve sigma [fst (EConstr.destEvar sigma ef)] in
  let sigma, (suchthat, impargs) = Constrintern.interp_type_evars_impls env' sigma ~impls suchthat in
  (* create the initial goals for the proof: |- Type ; |- ?1 ; f:=?2 |- suchthat *)
  let goals =
    let open Proofview in
        TCons ( env , sigma , f_type , (fun sigma ef' ->
            let sigma = Evd.define (fst (EConstr.destEvar sigma ef')) ef sigma in
            TCons ( env' , sigma , suchthat , (fun sigma _ -> TNil sigma)))) in
  let info = Declare.Info.make ~poly ~scope ?clearbody ~kind ?typing_flags ?user_warns () in  (* TODO: udecl *)
  let cinfo = Declare.CInfo.[make ~name:f ~typ:() ~impargs:f_impargs (); make ~name ~typ:() ~impargs ()] in
  let lemma = Declare.Proof.start_derive ~name ~f ~info ~cinfo goals in
  Declare.Proof.map lemma ~f:(fun p ->
      Util.pi1 @@ Proof.run_tactic env Proofview.(tclFOCUS 1 1 shelve) p)
