(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let map_const_entry_body (f:Term.constr->Term.constr) (x:Entries.const_entry_body)
    : Entries.const_entry_body =
  Future.chain ~pure:true x begin fun ((b,ctx),fx) ->
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
  (* create a sort variable for the type of [f] *)
  (* spiwack: I don't know what the rigidity flag does, picked the one
     that looked the most general. *)
  let (sigma,f_type_sort) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  let f_type_type = Term.mkSort f_type_sort in
  let goals =
    let open Proofview in
        TCons ( env , sigma , f_type_type , (fun sigma f_type ->
        TCons ( env , sigma , f_type , (fun sigma ef ->
        let env' = Environ.push_named (f , (Some ef) , f_type) env in
        let evdref = ref sigma in
        let suchthat = Constrintern.interp_type_evars evdref env' suchthat in
        TCons ( env' , !evdref , suchthat , (fun sigma _ ->
        TNil sigma))))))
    in
    let terminator com =
      let open Proof_global in
      match com with
      | Admitted -> Errors.error"Admitted isn't supported in Derive."
      | Proved (_,Some _,_) ->
          Errors.error"Cannot save a proof of Derive with an explicit name."
      | Proved (opaque, None, obj) ->
          let (f_def,lemma_def) =
            match Proof_global.(obj.entries) with
            | [_;f_def;lemma_def] ->
                f_def , lemma_def
            | _ -> assert false
          in
          (* The opacity of [f_def] is adjusted to be [false]. *)
          let f_def = let open Entries in { f_def with
          const_entry_opaque = false ; }
        in
        let f_def = Entries.DefinitionEntry f_def , Decl_kinds.(IsDefinition Definition) in
        let f_kn = Declare.declare_constant f f_def in
        let f_kn_term = Term.mkConst f_kn in
        let lemma_pretype =
          match Entries.(lemma_def.const_entry_type) with
          | Some t -> t
          | None -> assert false (* Proof_global always sets type here. *)
        in
        (* substitutes the variable [f] by the constant [f] it was standing for. *)
        let lemma_type = Vars.replace_vars [f,f_kn_term] lemma_pretype in
        (* The type of [lemma_def] is adjusted to refer to [f_kn], the
           opacity is adjusted by the proof ending command.  *)
        let lemma_body =
          map_const_entry_body begin fun c ->
            Vars.replace_vars [f,f_kn_term] c
          end Entries.(lemma_def.const_entry_body)
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
  let () = Proof_global.start_dependent_proof lemma kind goals terminator in
  let _ = Proof_global.with_current_proof begin fun _ p ->
    Proof.run_tactic env Proofview.(tclFOCUS 1 2 shelve) p
  end in
  ()




