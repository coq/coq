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

(** [start_deriving f suchthat lemma] starts a proof of [suchthat]
    (which can contain references to [f]) in the context extended by
    [f:=?x]. When the proof ends, [f] is defined as the value of [?x]
    and [lemma] as the proof. *)
let start_deriving f typ suchthat name : Declare.Proof.t =

  let env = Global.env () in
  let sigma = Evd.from_env env in
  let kind = Decls.(IsDefinition Definition) in

  (* create a sort variable for the type of [f] *)
  (* spiwack: I don't know what the rigidity flag does, picked the one
     that looked the most general. *)
  let (sigma,f_type_sort) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  let f_type_type = EConstr.mkSort f_type_sort in
  (* create the initial goals for the proof: |- Type ; |- ?1 ; f:=?2 |- suchthat *)
  let goals =
    let open Proofview in
    TCons ( env , sigma , f_type_type , (fun sigma f_type ->
        let sigma = match typ with
          | None -> sigma
          | Some typ ->
            let sigma, typ = Constrintern.interp_type_evars ~program_mode:false env sigma typ in
            Evd.define (fst (EConstr.destEvar sigma f_type)) typ sigma in
        TCons ( env , sigma , f_type , (fun sigma ef ->
            let env' = EConstr.push_named (LocalDef (EConstr.annotR f, ef, f_type)) env in
            let sigma, suchthat = Constrintern.interp_type_evars ~program_mode:false env' sigma suchthat in
            TCons ( env' , sigma , suchthat , (fun sigma _ ->
                TNil sigma))))))
  in
  let info = Declare.Info.make ~poly:false ~kind () in
  let lemma = Declare.Proof.start_derive ~name ~f ~info goals in
  Declare.Proof.map lemma ~f:(fun p ->
      Util.pi1 @@ Proof.run_tactic env Proofview.(tclFOCUS 1 2 shelve) p)
