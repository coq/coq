(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Context
open Context.Named.Declaration

(** [start_deriving f suchthat lemma] starts a proof of [suchthat]
    (which can contain references to [f]) in the context extended by
    [f:=?x]. When the proof ends, [f] is defined as the value of [?x]
    and [lemma] as the proof. *)
let start_deriving f suchthat name : Lemmas.t =

  let env = Global.env () in
  let sigma = Evd.from_env env in
  let poly = false in
  let kind = Decl_kinds.(DefinitionBody Definition) in

  (* create a sort variable for the type of [f] *)
  (* spiwack: I don't know what the rigidity flag does, picked the one
     that looked the most general. *)
  let (sigma,f_type_sort) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  let f_type_type = EConstr.mkSort f_type_sort in
  (* create the initial goals for the proof: |- Type ; |- ?1 ; f:=?2 |- suchthat *)
  let goals =
    let open Proofview in
    TCons ( env , sigma , f_type_type , (fun sigma f_type ->
        TCons ( env , sigma , f_type , (fun sigma ef ->
            let f_type = EConstr.Unsafe.to_constr f_type in
            let ef = EConstr.Unsafe.to_constr ef in
            let env' = Environ.push_named (LocalDef (annotR f, ef, f_type)) env in
            let sigma, suchthat = Constrintern.interp_type_evars ~program_mode:false env' sigma suchthat in
            TCons ( env' , sigma , suchthat , (fun sigma _ ->
                TNil sigma))))))
  in

  let info = Lemmas.Info.make ~proof_ending:(Lemmas.Proof_ending.(End_derive {f; name})) ~kind () in
  let lemma = Lemmas.start_dependent_lemma ~name ~poly ~info goals in
  Lemmas.pf_map (Proof_global.map_proof begin fun p ->
    Util.pi1 @@ Proof.run_tactic env Proofview.(tclFOCUS 1 2 shelve) p
  end) lemma
