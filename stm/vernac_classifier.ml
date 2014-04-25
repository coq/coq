(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Errors
open Pp

let string_of_in_script b = if b then " (inside script)" else ""

let string_of_vernac_type = function
  | VtUnknown -> "Unknown"
  | VtStartProof _ -> "StartProof"
  | VtSideff _ -> "Sideff"
  | VtQed VtKeep -> "Qed(keep)"
  | VtQed VtDrop -> "Qed(drop)"
  | VtProofStep -> "ProofStep"
  | VtProofMode s -> "ProofMode " ^ s
  | VtQuery b -> "Query" ^ string_of_in_script b
  | VtStm ((VtFinish|VtJoinDocument|VtObserve _|VtPrintDag|VtWait), b) ->
      "Stm" ^ string_of_in_script b
  | VtStm (VtPG, b) -> "Stm PG" ^ string_of_in_script b
  | VtStm (VtBack _, b) -> "Stm Back" ^ string_of_in_script b

let string_of_vernac_when = function
  | VtLater -> "Later"
  | VtNow -> "Now"

let string_of_vernac_classification (t,w) =
  string_of_vernac_type t ^ " " ^ string_of_vernac_when w

let classifiers = ref []
let declare_vernac_classifier
  (s : string)
  (f : Genarg.raw_generic_argument list -> unit -> vernac_classification)
=
  classifiers := !classifiers @ [s,f]

let elide_part_of_script_and_now (a, _) =
  match a with
  | VtQuery _ -> VtQuery false, VtNow
  | VtStm (x, _) -> VtStm (x, false), VtNow
  | x -> x, VtNow

let undo_classifier = ref (fun _ -> assert false)
let set_undo_classifier f = undo_classifier := f

let rec classify_vernac e =
  let static_classifier e = match e with
    (* PG compatibility *)
    | VernacUnsetOption (["Silent"]|["Undo"]|["Printing";"Depth"])
    | VernacSetOption   ((["Silent"]|["Undo"]|["Printing";"Depth"]),_)
      when !Flags.print_emacs -> VtStm(VtPG,false), VtNow
    (* Stm *)
    | VernacStm Finish -> VtStm (VtFinish, true), VtNow
    | VernacStm Wait -> VtStm (VtWait, true), VtNow
    | VernacStm JoinDocument -> VtStm (VtJoinDocument, true), VtNow
    | VernacStm PrintDag -> VtStm (VtPrintDag, true), VtNow
    | VernacStm (Observe id) -> VtStm (VtObserve id, true), VtNow
    | VernacStm (Command x) -> elide_part_of_script_and_now (classify_vernac x)
    | VernacStm (PGLast x) -> fst (classify_vernac x), VtNow
    (* Nested vernac exprs *)
    | VernacProgram e -> classify_vernac e
    | VernacLocal (_,e) -> classify_vernac e
    | VernacTimeout (_,e) -> classify_vernac e
    | VernacTime e -> classify_vernac e
    | VernacFail e -> (* Fail Qed or Fail Lemma must not join/fork the DAG *)
        (match classify_vernac e with
        | ( VtQuery _ | VtProofStep | VtSideff _
          | VtStm _ | VtProofMode _ ), _ as x -> x
        | VtQed _, _ -> VtProofStep, VtNow
        | (VtStartProof _ | VtUnknown), _ -> VtUnknown, VtNow)
    (* Qed *)
    | VernacEndProof Admitted | VernacAbort _ -> VtQed VtDrop, VtLater
    | VernacEndProof _ | VernacExactProof _ -> VtQed VtKeep, VtLater
    (* Query *)
    | VernacShow _ | VernacPrint _ | VernacSearch _ | VernacLocate _
    | VernacCheckMayEval _ -> VtQuery true, VtLater
    (* ProofStep *)
    | VernacProof _ 
    | VernacBullet _ 
    | VernacFocus _ | VernacUnfocus
    | VernacSubproof _ | VernacEndSubproof 
    | VernacSolve _ | VernacError _
    | VernacCheckGuard
    | VernacUnfocused
    | VernacSolveExistential _ -> VtProofStep, VtLater
    (* Options changing parser *)
    | VernacUnsetOption (["Default";"Proof";"Using"])
    | VernacSetOption (["Default";"Proof";"Using"],_) -> VtSideff [], VtNow
    (* StartProof *)
    | VernacDefinition (_,(_,i),ProveBody _) ->
        VtStartProof("Classic",GuaranteesOpacity,[i]), VtLater
    | VernacStartTheoremProof (_,l,_) ->
        let ids = 
          CList.map_filter (function (Some(_,i), _) -> Some i | _ -> None) l in
        VtStartProof ("Classic",GuaranteesOpacity,ids), VtLater
    | VernacGoal _ -> VtStartProof ("Classic",GuaranteesOpacity,[]), VtLater
    | VernacFixpoint (_,l) ->
        let ids, open_proof =
          List.fold_left (fun (l,b) (((_,id),_,_,_,p),_) ->
            id::l, b || p = None) ([],false) l in
        if open_proof then VtStartProof ("Classic",GuaranteesOpacity,ids), VtLater
        else VtSideff ids, VtLater
    | VernacCoFixpoint (_,l) ->
        let ids, open_proof =
          List.fold_left (fun (l,b) (((_,id),_,_,p),_) ->
            id::l, b || p = None) ([],false) l in
        if open_proof then VtStartProof ("Classic",GuaranteesOpacity,ids), VtLater
        else VtSideff ids, VtLater
    (* Sideff: apply to all open branches. usually run on master only *)
    | VernacAssumption (_,_,l) ->
        let ids = List.flatten (List.map (fun (_,(l,_)) -> List.map snd l) l) in
        VtSideff ids, VtLater    
    | VernacDefinition (_,(_,id),DefineBody _) -> VtSideff [id], VtLater
    | VernacInductive (_,_,l) ->
        let ids = List.map (fun (((_,(_,id)),_,_,_,cl),_) -> id :: match cl with
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
    | VernacRegister _
    | VernacComments _ -> VtSideff [], VtLater
    (* Who knows *)
    | VernacList _
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
    | VernacInfix _ | VernacNotation _ | VernacSyntaxExtension _ 
    | VernacSyntacticDefinition _
    | VernacDeclareTacticDefinition _ | VernacTacticNotation _
    | VernacRequire _ | VernacImport _ | VernacInclude _
    | VernacDeclareMLModule _
    | VernacContext _ (* TASSI: unsure *)
    | VernacProofMode _ 
    (* These are ambiguous *)
    | VernacInstance _ -> VtUnknown, VtNow
    (* Stm will install a new classifier to handle these *)
    | VernacBack _ | VernacAbortAll
    | VernacUndoTo _ | VernacUndo _
    | VernacResetName _ | VernacResetInitial
    | VernacBacktrack _ | VernacBackTo _ | VernacRestart -> !undo_classifier e
    (* What are these? *)
    | VernacNop
    | VernacToplevelControl _
    | VernacRestoreState _
    | VernacWriteState _ -> VtUnknown, VtNow
    (* Plugins should classify their commands *)
    | VernacExtend (s,l) ->
        try List.assoc s !classifiers l ()
        with Not_found -> anomaly(str"No classifier for"++spc()++str s)
  in
    static_classifier e

let classify_as_query = VtQuery true, VtLater
let classify_as_sideeff = VtSideff [], VtLater
