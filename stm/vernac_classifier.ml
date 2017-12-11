(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open CErrors
open Pp

let default_proof_mode () = Proof_global.get_default_proof_mode_name () [@ocaml.warning "-3"]

let string_of_in_script b = if b then " (inside script)" else ""

let string_of_parallel = function
  | `Yes (solve,abs) ->
       "par" ^ if solve then "solve" else "" ^ if abs then "abs" else ""
  | `No -> ""

let string_of_vernac_type = function
  | VtUnknown -> "Unknown"
  | VtStartProof _ -> "StartProof"
  | VtSideff _ -> "Sideff"
  | VtQed VtKeep -> "Qed(keep)"
  | VtQed VtKeepAsAxiom -> "Qed(admitted)"
  | VtQed VtDrop -> "Qed(drop)"
  | VtProofStep { parallel; proof_block_detection } ->
      "ProofStep " ^ string_of_parallel parallel ^
        Option.default "" proof_block_detection
  | VtProofMode s -> "ProofMode " ^ s
  | VtQuery (b, route) -> "Query " ^ string_of_in_script b ^ " route " ^ string_of_int route
  | VtMeta -> "Meta "

let string_of_vernac_when = function
  | VtLater -> "Later"
  | VtNow -> "Now"

let string_of_vernac_classification (t,w) =
  string_of_vernac_type t ^ " " ^ string_of_vernac_when w

let classifiers = ref []
let declare_vernac_classifier
  (s : Vernacexpr.extend_name)
  (f : Genarg.raw_generic_argument list -> unit -> vernac_classification)
=
  classifiers := !classifiers @ [s,f]

let make_polymorphic (a, b as x) =
  match a with
  | VtStartProof (x, _, ids) ->
      VtStartProof (x, Doesn'tGuaranteeOpacity, ids), b
  | _ -> x

let rec classify_vernac e =
  let static_classifier e = match e with
    (* Univ poly compatibility: we run it now, so that we can just
     * look at Flags in stm.ml.  Would be nicer to have the stm
     * look at the entire dag to detect this option. *)
    | VernacSetOption (["Universe"; "Polymorphism"],_)
    | VernacUnsetOption (["Universe"; "Polymorphism"]) -> VtSideff [], VtNow
    (* Nested vernac exprs *)
    | VernacProgram e -> classify_vernac e
    | VernacLocal (_,e) -> classify_vernac e
    | VernacPolymorphic (b, e) -> 
      if b || Flags.is_universe_polymorphism () (* Ok or not? *) then
	make_polymorphic (classify_vernac e)
      else classify_vernac e
    | VernacTimeout (_,e) -> classify_vernac e
    | VernacTime (_,e) | VernacRedirect (_, (_,e)) -> classify_vernac e
    | VernacFail e -> (* Fail Qed or Fail Lemma must not join/fork the DAG *)
        (match classify_vernac e with
        | ( VtQuery _ | VtProofStep _ | VtSideff _
          | VtProofMode _ | VtMeta), _ as x -> x
        | VtQed _, _ ->
            VtProofStep { parallel = `No; proof_block_detection = None },
            VtNow
        | (VtStartProof _ | VtUnknown), _ -> VtUnknown, VtNow)
    (* Qed *)
    | VernacAbort _ -> VtQed VtDrop, VtLater
    | VernacEndProof Admitted -> VtQed VtKeepAsAxiom, VtLater
    | VernacEndProof _ | VernacExactProof _ -> VtQed VtKeep, VtLater
    (* Query *)
    | VernacShow _ | VernacPrint _ | VernacSearch _ | VernacLocate _
    | VernacCheckMayEval _ -> VtQuery (true,Feedback.default_route), VtLater
    (* ProofStep *)
    | VernacProof _ 
    | VernacFocus _ | VernacUnfocus
    | VernacSubproof _
    | VernacCheckGuard
    | VernacUnfocused
    | VernacSolveExistential _ ->
        VtProofStep { parallel = `No; proof_block_detection = None }, VtLater
    | VernacBullet _ ->
        VtProofStep { parallel = `No; proof_block_detection = Some "bullet" },
        VtLater
    | VernacEndSubproof -> 
        VtProofStep { parallel = `No;
                      proof_block_detection = Some "curly" },
        VtLater
    (* Options changing parser *)
    | VernacUnsetOption (["Default";"Proof";"Using"])
    | VernacSetOption (["Default";"Proof";"Using"],_) -> VtSideff [], VtNow
    (* StartProof *)
    | VernacDefinition ((Decl_kinds.DoDischarge,_),((_,i),_),ProveBody _) ->
        VtStartProof(default_proof_mode (),Doesn'tGuaranteeOpacity,[i]), VtLater
    | VernacDefinition (_,((_,i),_),ProveBody _) ->
        VtStartProof(default_proof_mode (),GuaranteesOpacity,[i]), VtLater
    | VernacStartTheoremProof (_,l) ->
        let ids = 
          CList.map_filter (function (Some ((_,i),pl), _) -> Some i | _ -> None) l in
        VtStartProof (default_proof_mode (),GuaranteesOpacity,ids), VtLater
    | VernacGoal _ -> VtStartProof (default_proof_mode (),GuaranteesOpacity,[]), VtLater
    | VernacFixpoint (discharge,l) ->
       let guarantee =
         match discharge with
         | Decl_kinds.NoDischarge -> GuaranteesOpacity
         | Decl_kinds.DoDischarge -> Doesn'tGuaranteeOpacity
       in
        let ids, open_proof =
          List.fold_left (fun (l,b) ((((_,id),_),_,_,_,p),_) ->
            id::l, b || p = None) ([],false) l in
        if open_proof
        then VtStartProof (default_proof_mode (),guarantee,ids), VtLater
        else VtSideff ids, VtLater
    | VernacCoFixpoint (discharge,l) ->
       let guarantee =
         match discharge with
         | Decl_kinds.NoDischarge -> GuaranteesOpacity
         | Decl_kinds.DoDischarge -> Doesn'tGuaranteeOpacity
       in
        let ids, open_proof =
          List.fold_left (fun (l,b) ((((_,id),_),_,_,p),_) ->
            id::l, b || p = None) ([],false) l in
        if open_proof
        then VtStartProof (default_proof_mode (),guarantee,ids), VtLater
        else VtSideff ids, VtLater
    (* Sideff: apply to all open branches. usually run on master only *)
    | VernacAssumption (_,_,l) ->
        let ids = List.flatten (List.map (fun (_,(l,_)) -> List.map (fun (id, _) -> snd id) l) l) in
        VtSideff ids, VtLater    
    | VernacDefinition (_,((_,id),_),DefineBody _) -> VtSideff [id], VtLater
    | VernacInductive (_, _,_,l) ->
        let ids = List.map (fun (((_,((_,id),_)),_,_,_,cl),_) -> id :: match cl with
        | Constructors l -> List.map (fun (_,((_,id),_)) -> id) l
        | RecordDecl (oid,l) -> (match oid with Some (_,x) -> [x] | _ -> []) @
           CList.map_filter (function
            | ((_,AssumExpr((_,Names.Name n),_)),_),_ -> Some n
            | _ -> None) l) l in
        VtSideff (List.flatten ids), VtLater
    | VernacScheme l ->
        let ids = List.map snd (CList.map_filter (fun (x,_) -> x) l) in
        VtSideff ids, VtLater
    | VernacCombinedScheme ((_,id),_) -> VtSideff [id], VtLater
    | VernacBeginSection (_,id) -> VtSideff [id], VtLater
    | VernacUniverse _ | VernacConstraint _
    | VernacCanonical _ | VernacCoercion _ | VernacIdentityCoercion _
    | VernacAddLoadPath _ | VernacRemoveLoadPath _ | VernacAddMLPath _
    | VernacChdir _ 
    | VernacCreateHintDb _ | VernacRemoveHints _ | VernacHints _
    | VernacDeclareImplicits _ | VernacArguments _ | VernacArgumentsScope _
    | VernacReserve _
    | VernacGeneralizable _
    | VernacSetOpacity _ | VernacSetStrategy _
    | VernacUnsetOption _ | VernacSetOption _ | VernacSetAppendOption _
    | VernacAddOption _ | VernacRemoveOption _
    | VernacMemOption _ | VernacPrintOption _
    | VernacGlobalCheck _
    | VernacDeclareReduction _
    | VernacDeclareClass _ | VernacDeclareInstances _
    | VernacRegister _
    | VernacNameSectionHypSet _
    | VernacComments _ -> VtSideff [], VtLater
    (* Who knows *)
    | VernacLoad _ -> VtSideff [], VtNow
    (* (Local) Notations have to disappear *)
    | VernacEndSegment _ -> VtSideff [], VtNow
    (* Modules with parameters have to be executed: can import notations *)
    | VernacDeclareModule (exp,(_,id),bl,_)
    | VernacDefineModule (exp,(_,id),bl,_,_) ->
        VtSideff [id], if bl = [] && exp = None then VtLater else VtNow
    | VernacDeclareModuleType ((_,id),bl,_,_) ->
        VtSideff [id], if bl = [] then VtLater else VtNow
    (* These commands alter the parser *)
    | VernacOpenCloseScope _ | VernacDelimiters _ | VernacBindScope _
    | VernacInfix _ | VernacNotation _ | VernacNotationAddFormat _
    | VernacSyntaxExtension _
    | VernacSyntacticDefinition _
    | VernacRequire _ | VernacImport _ | VernacInclude _
    | VernacDeclareMLModule _
    | VernacContext _ (* TASSI: unsure *)
    | VernacProofMode _ -> VtSideff [], VtNow
    (* These are ambiguous *)
    | VernacInstance _ -> VtUnknown, VtNow
    (* Stm will install a new classifier to handle these *)
    | VernacBack _ | VernacAbortAll
    | VernacUndoTo _ | VernacUndo _
    | VernacResetName _ | VernacResetInitial
    | VernacBacktrack _ | VernacBackTo _ | VernacRestart -> VtMeta, VtNow
    (* What are these? *)
    | VernacToplevelControl _
    | VernacRestoreState _
    | VernacWriteState _ -> VtSideff [], VtNow
    (* Plugins should classify their commands *)
    | VernacExtend (s,l) ->
        try List.assoc s !classifiers l ()
        with Not_found -> anomaly(str"No classifier for"++spc()++str (fst s)++str".")
  in
  let res = static_classifier e in
    if Flags.is_universe_polymorphism () then
      make_polymorphic res
    else res

let classify_as_query = VtQuery (true,Feedback.default_route), VtLater
let classify_as_sideeff = VtSideff [], VtLater
let classify_as_proofstep = VtProofStep { parallel = `No; proof_block_detection = None}, VtLater
