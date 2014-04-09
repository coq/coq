(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let interp_init_def_and_relation env sigma init_def r =
  let init_def, _ = Constrintern.interp_constr sigma env init_def in
  let init_type = Typing.type_of env sigma init_def in

  let r_type =
    let open Term in
    mkProd (Names.Anonymous,init_type, mkProd (Names.Anonymous,init_type,mkProp))
  in
  let r, ctx = Constrintern.interp_casted_constr sigma env r r_type in
  init_def , init_type , r, Evd.evar_universe_context_set ctx
  

(** [start_deriving f init r lemma] starts a proof of [r init
    ?x]. When the proof ends, [f] is defined as the value of [?x] and
    [lemma] as the proof. *)
let start_deriving f init_def r lemma =
  let env = Global.env () in
  let kind = Decl_kinds.(Global,false,DefinitionBody Definition) in
  let ( init_def , init_type , r , ctx ) =
    interp_init_def_and_relation env Evd.empty init_def r
  in
  let goals =
    let open Proofview in
    TCons ( env , (init_type , ctx ) , (fun ef ->
      TCons ( env , ( Term.mkApp ( r , [| init_def ; ef |] ) , Univ.ContextSet.empty) , (fun _ -> TNil))))
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
          | [f_def;lemma_def] ->
              f_def , lemma_def
          | _ -> assert false
        in
        (* The opacity of [f_def] is adjusted to be [false]. *)
        let f_def = let open Entries in { f_def with
          const_entry_opaque = false ; }
        in
        let f_def = Entries.DefinitionEntry f_def , Decl_kinds.(IsDefinition Definition) in
        let f_kn = Declare.declare_constant f f_def in
        let lemma_typ = Term.(mkApp ( r , [| init_def ; mkConst f_kn |] )) in
        (* The type of [lemma_def] is adjusted to refer to [f_kn], the
           opacity is adjusted by the proof ending command.  *)
        let lemma_def = let open Entries in { lemma_def with
          const_entry_type = Some lemma_typ ;
          const_entry_opaque = opaque ; }
        in
        let lemma_def =
          Entries.DefinitionEntry lemma_def ,
          Decl_kinds.(IsProof Proposition)
        in
        ignore (Declare.declare_constant lemma lemma_def)
  in
  let () = Proof_global.start_dependent_proof
    lemma kind goals terminator
  in
  let _ = Proof_global.with_current_proof begin fun _ p ->
    Proof.run_tactic env Proofview.(tclFOCUS 1 1 shelve) p
  end in
  ()

