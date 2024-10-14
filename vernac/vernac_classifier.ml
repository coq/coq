(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open CAst
open Vernacextend
open Vernacexpr

let string_of_vernac_when = function
  | VtLater -> "Later"
  | VtNow -> "Now"

let string_of_vernac_classification = function
  | VtStartProof _ -> "StartProof"
  | VtSideff (_,w) -> "Sideff"^" "^(string_of_vernac_when w)
  | VtQed (VtKeep VtKeepAxiom) -> "Qed(admitted)"
  | VtQed (VtKeep (VtKeepOpaque | VtKeepDefined)) -> "Qed(keep)"
  | VtQed VtDrop -> "Qed(drop)"
  | VtProofStep {  proof_block_detection } ->
      "ProofStep " ^ Option.default "" proof_block_detection
  | VtQuery -> "Query"
  | VtMeta -> "Meta "
  | VtProofMode _ -> "Proof Mode"

let vtkeep_of_opaque = function
  | Opaque -> VtKeepOpaque
  | Transparent -> VtKeepDefined

let idents_of_name : Names.Name.t -> Names.Id.t list =
  function
  | Names.Anonymous -> []
  | Names.Name n -> [n]

let stm_allow_nested_proofs_option_name = ["Nested";"Proofs";"Allowed"]

let options_affecting_stm_scheduling =
  [ Attributes.universe_polymorphism_option_name;
    stm_allow_nested_proofs_option_name;
    Synterp.proof_mode_opt_name;
    Attributes.program_mode_option_name;
    Proof_using.proof_using_opt_name;
  ]

let classify_vernac e =
  let static_synterp_classifier ~atts e = match e with
    (* Univ poly compatibility: we run it now, so that we can just
     * look at Flags in stm.ml.  Would be nicer to have the stm
     * look at the entire dag to detect this option. *)
    | VernacSetOption (_, l,_)
      when CList.exists (CList.equal String.equal l)
        options_affecting_stm_scheduling ->
       VtSideff ([], VtNow)
    | VernacBeginSection {v=id} -> VtSideff ([id], VtLater)
    | VernacChdir _ | VernacExtraDependency _
    | VernacSetOption _ -> VtSideff ([], VtLater)
    (* (Local) Notations have to disappear *)
    | VernacEndSegment _ -> VtSideff ([], VtNow)
    (* Modules with parameters have to be executed: can import notations *)
    | VernacDeclareModule (exp,{v=id},bl,_)
    | VernacDefineModule (exp,{v=id},bl,_,_) ->
        VtSideff ([id], if bl = [] && exp = None then VtLater else VtNow)
    | VernacDeclareModuleType ({v=id},bl,_,_) ->
        VtSideff ([id], if bl = [] then VtLater else VtNow)
    (* These commands alter the parser *)
    | VernacDeclareCustomEntry _
    | VernacNotation _ | VernacReservedNotation _
    | VernacRequire _ | VernacImport _ | VernacInclude _
    | VernacDeclareMLModule _ -> VtSideff ([], VtNow)
    | VernacProofMode pm ->
      (match Pvernac.lookup_proof_mode pm with
      | None ->
        CErrors.user_err Pp.(str (Format.sprintf "No proof mode named \"%s\"." pm))
      | Some proof_mode -> VtProofMode proof_mode)
    (* Plugins should classify their commands *)
    | VernacLoad _ -> VtSideff ([], VtNow)
    | VernacExtend (s,l) ->
        try Vernacextend.get_vernac_classifier s l
        with Not_found -> anomaly(str"No classifier for"++spc()++str s.ext_entry ++str".")
  in
  let static_pure_classifier ~atts e = match e with
    (* Qed *)
    | VernacAbort -> VtQed VtDrop
    | VernacEndProof Admitted -> VtQed (VtKeep VtKeepAxiom)
    | VernacEndProof (Proved (opaque,_)) -> VtQed (VtKeep (vtkeep_of_opaque opaque))
    | VernacExactProof _ -> VtQed (VtKeep VtKeepOpaque)
    (* Query *)
    | VernacShow _ | VernacPrint _ | VernacSearch _ | VernacLocate _
    | VernacCheckGuard | VernacValidateProof
    | VernacGlobalCheck _ | VernacCheckMayEval _ -> VtQuery
    (* ProofStep *)
    | VernacProof _
    | VernacFocus _ | VernacUnfocus
    | VernacSubproof _
    | VernacUnfocused
    | VernacBullet _ ->
        VtProofStep { proof_block_detection = Some "bullet" }
    | VernacEndSubproof ->
        VtProofStep { proof_block_detection = Some "curly" }
    (* StartProof *)
    | VernacDefinition ((DoDischarge,_),({v=i},_),ProveBody _) ->
      VtStartProof(Doesn'tGuaranteeOpacity, idents_of_name i)

    | VernacDefinition (_,({v=i},_),ProveBody _) ->
      let polymorphic = Attributes.(parse_drop_extra polymorphic atts) in
      let guarantee = if polymorphic then Doesn'tGuaranteeOpacity else GuaranteesOpacity in
      VtStartProof(guarantee, idents_of_name i)
    | VernacStartTheoremProof (_,l) ->
      let polymorphic = Attributes.(parse_drop_extra polymorphic atts) in
      let ids = List.map (fun (({v=i}, _), _) -> i) l in
      let guarantee = if polymorphic then Doesn'tGuaranteeOpacity else GuaranteesOpacity in
      VtStartProof (guarantee,ids)
    | VernacFixpoint (discharge,(_,l)) ->
      let polymorphic = Attributes.(parse_drop_extra polymorphic atts) in
       let guarantee =
         if discharge = DoDischarge || polymorphic then Doesn'tGuaranteeOpacity
         else GuaranteesOpacity
       in
        let ids, open_proof =
          List.fold_left (fun (l,b) {Vernacexpr.fname={CAst.v=id}; body_def} ->
            id::l, b || body_def = None) ([],false) l in
        if open_proof
        then VtStartProof (guarantee,ids)
        else VtSideff (ids, VtLater)
    | VernacCoFixpoint (discharge,l) ->
      let polymorphic = Attributes.(parse_drop_extra polymorphic atts) in
       let guarantee =
         if discharge = DoDischarge || polymorphic then Doesn'tGuaranteeOpacity
         else GuaranteesOpacity
       in
        let ids, open_proof =
          List.fold_left (fun (l,b) { Vernacexpr.fname={CAst.v=id}; body_def } ->
            id::l, b || body_def = None) ([],false) l in
        if open_proof
        then VtStartProof (guarantee,ids)
        else VtSideff (ids, VtLater)
    (* Sideff: apply to all open branches. usually run on master only *)
    | VernacAssumption (_,_,l) ->
        let ids = List.flatten (List.map (fun (_,(l,_)) -> List.map (fun (id, _) -> id.v) l) l) in
        VtSideff (ids, VtLater)
    | VernacSymbol l ->
        let ids = List.flatten (List.map (fun (_,(l,_)) -> List.map (fun (id, _) -> id.v) l) l) in
        VtSideff (ids, VtLater)
    | VernacPrimitive ((id,_),_,_) ->
        VtSideff ([id.CAst.v], VtLater)
    | VernacDefinition (_,({v=id},_),DefineBody _) -> VtSideff (idents_of_name id, VtLater)
    | VernacInductive (_,l) ->
        let ids = List.map (fun (((_,({v=id},_)),_,_,cl),_) -> id :: match cl with
        | Constructors l -> List.map (fun (_,({v=id},_)) -> id) l
        | RecordDecl (oid,l,obinder) -> (match oid with Some {v=x} -> [x] | _ -> []) @
           (match obinder with Some {v=x} -> [x] | _ -> []) @
           CList.map_filter (function
            | AssumExpr({v=Names.Name n},_,_), _ -> Some n
            | _ -> None) l) l in
        VtSideff (List.flatten ids, VtLater)
    | VernacScheme l ->
        let ids = List.map (fun {v}->v) (CList.map_filter (fun (x,_) -> x) l) in
        VtSideff (ids, VtLater)
    | VernacCombinedScheme ({v=id},_) -> VtSideff ([id], VtLater)
    | VernacUniverse _ | VernacConstraint _
    | VernacCanonical _ | VernacCoercion _ | VernacIdentityCoercion _
    | VernacCreateHintDb _ | VernacRemoveHints _ | VernacHints _
    | VernacArguments _
    | VernacReserve _
    | VernacGeneralizable _
    | VernacSetOpacity _ | VernacSetStrategy _
    | VernacAddOption _ | VernacRemoveOption _
    | VernacMemOption _ | VernacPrintOption _
    | VernacDeclareReduction _
    | VernacExistingClass _ | VernacExistingInstance _
    | VernacRegister _
    | VernacNameSectionHypSet _
    | VernacComments _
    | VernacAttributes _
    | VernacSchemeEquality _
    | VernacAddRewRule _
    | VernacDeclareInstance _ -> VtSideff ([], VtLater)
    (* Who knows *)
    | VernacOpenCloseScope _ | VernacDeclareScope _
    | VernacDelimiters _ | VernacBindScope _
    | VernacEnableNotation _
    | VernacSyntacticDefinition _
    | VernacContext _ (* TASSI: unsure *) -> VtSideff ([], VtNow)
    | VernacInstance ((name,_),_,_,props,_) ->
      let program, refine =
        Attributes.(parse_drop_extra Notations.(program ++ Classes.refine_att) atts)
      in
      if program || (props <> None && not refine) then
        VtSideff (idents_of_name name.CAst.v, VtLater)
      else
        let polymorphic = Attributes.(parse_drop_extra polymorphic atts) in
        let guarantee = if polymorphic then Doesn'tGuaranteeOpacity else GuaranteesOpacity in
        VtStartProof (guarantee, idents_of_name name.CAst.v)
    (* Stm will install a new classifier to handle these *)
    | VernacBack _ | VernacAbortAll
    | VernacUndoTo _ | VernacUndo _
    | VernacResetName _ | VernacResetInitial
    | VernacRestart -> VtMeta
  in
  let static_classifier ~atts e = match e with
    | VernacSynPure e -> static_pure_classifier ~atts e
    | VernacSynterp e -> static_synterp_classifier ~atts e
  in
  let static_control_classifier ({ CAst.v ; _ } as cmd) =
    (* Fail Qed or Fail Lemma must not join/fork the DAG *)
    (* XXX why is Fail not always Query? *)
    if Vernacprop.has_query_control cmd then
      (match static_classifier ~atts:v.attrs v.expr with
         | VtQuery | VtProofStep _ | VtSideff _
         | VtMeta as x -> x
         | VtQed _ -> VtProofStep { proof_block_detection = None }
         | VtStartProof _ | VtProofMode _ -> VtQuery)
    else
      static_classifier ~atts:v.attrs v.expr

  in
  static_control_classifier e
