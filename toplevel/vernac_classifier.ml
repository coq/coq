(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Stateid
open Vernacexpr
open Errors
open Pp

let string_of_in_script b = if b then " (inside script)" else ""

let string_of_vernac_type = function
  | VtUnknown -> "Unknown"
  | VtStartProof _ -> "StartProof"
  | VtSideff -> "Sideff"
  | VtQed _ -> "Qed"
  | VtProofStep -> "ProofStep"
  | VtQuery b -> "Query" ^ string_of_in_script b
  | VtStm ((VtFinish|VtJoinDocument|VtObserve _), b) ->
      "Stm" ^ string_of_in_script b
  | VtStm (VtBack _, b) -> "Stm Back" ^ string_of_in_script b

let string_of_vernac_when = function
  | VtLater -> "Later"
  | VtNow -> "Now"

let string_of_vernac_classification (t,w) =
  string_of_vernac_type t ^ " " ^ string_of_vernac_when w

(* Since the set of vernaculars is extensible, also the classification function
   has to be. *)
let classifiers = Summary.ref ~name:"vernac_classifier" []
let declare_vernac_classifier s (f : vernac_expr -> vernac_classification) =
  classifiers := !classifiers @ [s,f]

let elide_part_of_script_and_now (a, _) =
  match a with
  | VtQuery _ -> VtQuery false, VtNow
  | VtStm (x, _) -> VtStm (x, false), VtNow
  | x -> x, VtNow

let rec classify_vernac e =
  let static_classifier e = match e with
    (* Stm *)
    | VernacStm Finish -> VtStm (VtFinish, true), VtNow
    | VernacStm JoinDocument -> VtStm (VtJoinDocument, true), VtNow
    | VernacStm (Observe id) -> VtStm (VtObserve id, true), VtNow
    | VernacStm (Command x) -> elide_part_of_script_and_now (classify_vernac x)
    (* Impossible, Vernac handles these *)
    | VernacList _ -> anomaly (str "VernacList not handled by Vernac")
    | VernacLoad _ -> anomaly (str "VernacLoad not handled by Vernac")
    (* Nested vernac exprs *)
    | VernacProgram e -> classify_vernac e
    | VernacLocal (_,e) -> classify_vernac e
    | VernacTimeout (_,e) -> classify_vernac e
    | VernacTime e -> classify_vernac e
    | VernacFail e -> (* Fail Qed or Fail Lemma must not join/fork the DAG *)
        (match classify_vernac e with
        | (VtQuery _ | VtProofStep _ | VtSideff _ | VtStm _), _ as x -> x
        | VtQed _, _ -> VtProofStep, VtNow
        | (VtStartProof _ | VtUnknown), _ -> VtUnknown, VtNow)
    (* Qed *)
    | VernacEndProof Admitted | VernacAbort _ -> VtQed DropProof, VtLater
    | VernacEndProof _ | VernacExactProof _ -> VtQed KeepProof, VtLater
    (* Query *)
    | VernacShow _ | VernacPrint _ | VernacSearch _ | VernacLocate _
    | VernacCheckMayEval _ -> VtQuery true, VtLater
    (* ProofStep *)
    | VernacProof _ 
    | VernacBullet _ 
    | VernacFocus _ | VernacUnfocus _
    | VernacSubproof _ | VernacEndSubproof _ 
    | VernacSolve _ 
    | VernacCheckGuard _
    | VernacUnfocused _
    | VernacSolveExistential _ -> VtProofStep, VtLater
    (* StartProof *)
    | VernacDefinition (_,(_,i),ProveBody _) ->
        VtStartProof("Classic",[i]), VtLater
    | VernacStartTheoremProof (_,l,_) ->
        let names = 
          CList.map_filter (function (Some(_,i), _) -> Some i | _ -> None) l in
        VtStartProof ("Classic", names), VtLater
    | VernacGoal _ -> VtStartProof ("Classic",[]), VtLater
    | VernacFixpoint (_,l)
      when List.exists (fun ((_,_,_,_,p),_) -> p = None) l ->
        VtStartProof ("Classic",
          List.map (fun (((_,id),_,_,_,_),_) -> id) l), VtLater
    | VernacCoFixpoint (_,l)
      when List.exists (fun ((_,_,_,p),_) -> p = None) l ->
        VtStartProof ("Classic",
          List.map (fun (((_,id),_,_,_),_) -> id) l), VtLater
    (* Sideff: apply to all open branches. usually run on master only *)
    | VernacAssumption _
    | VernacDefinition (_,_,DefineBody _)
    | VernacFixpoint _ | VernacCoFixpoint _
    | VernacInductive _
    | VernacScheme _ | VernacCombinedScheme _
    | VernacBeginSection _
    | VernacCanonical _ | VernacCoercion _ | VernacIdentityCoercion _
    | VernacAddLoadPath _ | VernacRemoveLoadPath _ | VernacAddMLPath _
    | VernacChdir _ 
    | VernacCreateHintDb _ | VernacRemoveHints _ | VernacHints _
    | VernacDeclareImplicits _ | VernacArguments _ | VernacArgumentsScope _
    | VernacReserve _
    | VernacGeneralizable _
    | VernacSetOpacity _ | VernacSetStrategy _
    | VernacUnsetOption _ | VernacSetOption _
    | VernacAddOption _ | VernacRemoveOption _
    | VernacMemOption _ | VernacPrintOption _
    | VernacGlobalCheck _
    | VernacDeclareReduction _
    | VernacDeclareClass _ | VernacDeclareInstances _
    | VernacComments _ -> VtSideff, VtLater
    (* (Local) Notations have to disappear *)
    | VernacEndSegment _ -> VtSideff, VtNow
    (* Modules with parameters have to be executed: can import notations *)
    | VernacDeclareModule (_,_,bl,_)
    | VernacDefineModule (_,_,bl,_,_)
    | VernacDeclareModuleType (_,bl,_,_) ->
        VtSideff, if bl = [] then VtLater else VtNow
    (* These commands alter the parser *)
    | VernacOpenCloseScope _ | VernacDelimiters _ | VernacBindScope _
    | VernacInfix _ | VernacNotation _ | VernacSyntaxExtension _ 
    | VernacSyntacticDefinition _
    | VernacDeclareTacticDefinition _ | VernacTacticNotation _
    | VernacRequire _ | VernacImport _ | VernacInclude _
    | VernacDeclareMLModule _
    | VernacContext _ (* TASSI: unsure *)
    | VernacProofMode _ 
    | VernacRequireFrom _ -> VtSideff, VtNow
    (* These are ambiguous *)
    | VernacInstance _ -> VtUnknown, VtNow
    (* Stm will install a new classifier to handle these *)
    | VernacBack _ | VernacAbortAll
    | VernacUndoTo _ | VernacUndo _
    | VernacResetName _ | VernacResetInitial _
    | VernacBacktrack _ | VernacBackTo _ | VernacRestart -> !undo_classifier e
    (* What are these? *)
    | VernacNop
    | VernacToplevelControl _
    | VernacRestoreState _
    | VernacWriteState _ -> VtUnknown, VtNow
    (* Plugins should classify their commands *)
    | VernacExtend _ -> VtUnknown, VtNow in
  let rec extended_classifier = function
    | [] -> static_classifier e
    | (name,f)::fs -> 
        try
          match f e with
          | VtUnknown, _ -> extended_classifier fs
          | x -> x
        with e when Errors.noncritical e ->
          let e = Errors.push e in
          msg_warning(str"Exception raised by classifier: " ++ str name);
          raise e

  in
  extended_classifier !classifiers

