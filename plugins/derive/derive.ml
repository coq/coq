(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Context.Named.Declaration

let map_const_entry_body (f:constr->constr) (x:Safe_typing.private_constants Entries.const_entry_body)
    : Safe_typing.private_constants Entries.const_entry_body =
  Future.chain x begin fun ((b,ctx),fx) ->
    (f b , ctx) , fx
  end

(** [start_deriving f suchthat lemma] starts a proof of [suchthat]
    (which can contain references to [f]) in the context extended by
    [f:=?x]. When the proof ends, [f] is defined as the value of [?x]
    and [lemma] as the proof. *)
let start_deriving f suchthat lemma =

  let env = Global.env () in
  let sigma = Evd.from_env env in
  let kind = Decl_kinds.(Global,false,DefinitionBody Definition) in

  (** create a sort variable for the type of [f] *)
  (* spiwack: I don't know what the rigidity flag does, picked the one
     that looked the most general. *)
  let (sigma,f_type_sort) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  let f_type_type = EConstr.mkSort f_type_sort in
  (** create the initial goals for the proof: |- Type ; |- ?1 ; f:=?2 |- suchthat *)
  let goals =
    let open Proofview in
        TCons ( env , sigma , f_type_type , (fun sigma f_type ->
        TCons ( env , sigma , f_type , (fun sigma ef ->
        let f_type = EConstr.Unsafe.to_constr f_type in
        let ef = EConstr.Unsafe.to_constr ef in
        let env' = Environ.push_named (LocalDef (f, ef, f_type)) env in
        let sigma, suchthat = Constrintern.interp_type_evars env' sigma suchthat in
        TCons ( env' , sigma , suchthat , (fun sigma _ ->
        TNil sigma))))))
    in

    (** The terminator handles the registering of constants when the proof is closed. *)
    let terminator com =
      let open Proof_global in
      (** Extracts the relevant information from the proof. [Admitted]
          and [Save] result in user errors. [opaque] is [true] if the
          proof was concluded by [Qed], and [false] if [Defined]. [f_def]
          and [lemma_def] correspond to the proof of [f] and of
          [suchthat], respectively. *)
      let (opaque,f_def,lemma_def) =
        match com with
        | Admitted _ -> CErrors.user_err Pp.(str "Admitted isn't supported in Derive.")
        | Proved (_,Some _,_) ->
            CErrors.user_err Pp.(str "Cannot save a proof of Derive with an explicit name.")
        | Proved (opaque, None, obj) ->
            match Proof_global.(obj.entries) with
            | [_;f_def;lemma_def] ->
                opaque <> Proof_global.Transparent , f_def , lemma_def
            | _ -> assert false
      in
      (** The opacity of [f_def] is adjusted to be [false], as it
          must. Then [f] is declared in the global environment. *)
      let f_def = { f_def with Entries.const_entry_opaque = false } in
      let f_def = Entries.DefinitionEntry f_def , Decl_kinds.(IsDefinition Definition) in
      let f_kn = Declare.declare_constant f f_def in
      let f_kn_term = mkConst f_kn in
      (** In the type and body of the proof of [suchthat] there can be
          references to the variable [f]. It needs to be replaced by
          references to the constant [f] declared above. This substitution
          performs this precise action. *)
      let substf c = Vars.replace_vars [f,f_kn_term] c in
      (** Extracts the type of the proof of [suchthat]. *)
      let lemma_pretype =
        match Entries.(lemma_def.const_entry_type) with
        | Some t -> t
        | None -> assert false (* Proof_global always sets type here. *)
      in
      (** The references of [f] are subsituted appropriately. *)
      let lemma_type = substf lemma_pretype in
      (** The same is done in the body of the proof. *)
      let lemma_body =
        map_const_entry_body substf Entries.(lemma_def.const_entry_body)
      in
      let lemma_def = let open Entries in { lemma_def with
        const_entry_body = lemma_body ;
        const_entry_type = Some lemma_type ;
        const_entry_opaque = opaque ; }
      in
      let lemma_def =
        Entries.DefinitionEntry lemma_def ,
        Decl_kinds.(IsProof Proposition)
      in
      ignore (Declare.declare_constant lemma lemma_def)
      in

  let terminator = Proof_global.make_terminator terminator in
  let () = Proof_global.start_dependent_proof lemma kind goals terminator in
  let _ = Proof_global.with_current_proof begin fun _ p ->
    Proof.run_tactic env Proofview.(tclFOCUS 1 2 shelve) p
  end in
  ()




