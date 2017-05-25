(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constrexpr
open Vernacexpr
open Misctypes

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Vernac_

let thm_token = G_vernac.thm_token

let hint_proof_using e = function
  | Some _ as x -> x
  | None -> match Proof_using.get_default_proof_using () with
     | None -> None
     | Some s -> Some (Gram.entry_parse e (Gram.parsable (Stream.of_string s)))

let hint = Gram.entry_create "hint"

(* Proof commands *)
GEXTEND Gram
  GLOBAL: hint command;

  opt_hintbases:
  [ [ -> []
    | ":"; l = LIST1 [id = IDENT -> id ] -> l ] ]
  ;
  command:
    [ [ IDENT "Goal"; c = lconstr -> VernacGoal c
      | IDENT "Proof" ->
          VernacProof (None,hint_proof_using G_vernac.section_subset_expr None)
      | IDENT "Proof" ; IDENT "Mode" ; mn = string -> VernacProofMode mn
      | IDENT "Proof"; c = lconstr -> VernacExactProof c
      | IDENT "Abort" -> VernacAbort None
      | IDENT "Abort"; IDENT "All" -> VernacAbortAll
      | IDENT "Abort"; id = identref -> VernacAbort (Some id)
      | IDENT "Existential"; n = natural; c = constr_body ->
	  VernacSolveExistential (n,c)
      | IDENT "Admitted" -> VernacEndProof Admitted
      | IDENT "Qed" -> VernacEndProof (Proved (Opaque None,None))
      | IDENT "Qed"; IDENT "exporting"; l = LIST0 identref SEP "," ->
          VernacEndProof (Proved (Opaque (Some l),None))
      | IDENT "Save"; id = identref ->
	  VernacEndProof (Proved (Opaque None, Some id))
      | IDENT "Defined" -> VernacEndProof (Proved (Transparent,None))
      |	IDENT "Defined"; id=identref ->
	  VernacEndProof (Proved (Transparent,Some id))
      | IDENT "Restart" -> VernacRestart
      | IDENT "Undo" -> VernacUndo 1
      | IDENT "Undo"; n = natural -> VernacUndo n
      | IDENT "Undo"; IDENT "To"; n = natural -> VernacUndoTo n
      | IDENT "Focus" -> VernacFocus None
      | IDENT "Focus"; n = natural -> VernacFocus (Some n)
      | IDENT "Unfocus" -> VernacUnfocus
      | IDENT "Unfocused" -> VernacUnfocused
      | IDENT "Show" -> VernacShow (ShowGoal OpenSubgoals)
      | IDENT "Show"; n = natural -> VernacShow (ShowGoal (NthGoal n))
      | IDENT "Show"; id = ident -> VernacShow (ShowGoal (GoalId id))
      | IDENT "Show"; IDENT "Goal" -> VernacShow (ShowGoal (GoalId (Names.Id.of_string "Goal")))
      | IDENT "Show"; IDENT "Goal"; n = string ->
          VernacShow (ShowGoal (GoalUid n))
      | IDENT "Show"; IDENT "Implicit"; IDENT "Arguments"; n = OPT natural ->
	  VernacShow (ShowGoalImplicitly n)
      | IDENT "Show"; IDENT "Node" -> VernacShow ShowNode
      | IDENT "Show"; IDENT "Script" -> VernacShow ShowScript
      | IDENT "Show"; IDENT "Existentials" -> VernacShow ShowExistentials
      | IDENT "Show"; IDENT "Universes" -> VernacShow ShowUniverses
      | IDENT "Show"; IDENT "Tree" -> VernacShow ShowTree
      | IDENT "Show"; IDENT "Conjectures" -> VernacShow ShowProofNames
      | IDENT "Show"; IDENT "Proof" -> VernacShow ShowProof
      | IDENT "Show"; IDENT "Intro" -> VernacShow (ShowIntros false)
      | IDENT "Show"; IDENT "Intros" -> VernacShow (ShowIntros true)
      | IDENT "Show"; IDENT "Match"; id = reference -> VernacShow (ShowMatch id)
      | IDENT "Show"; IDENT "Thesis" -> VernacShow ShowThesis
      | IDENT "Guarded" -> VernacCheckGuard
      (* Hints for Auto and EAuto *)
      | IDENT "Create"; IDENT "HintDb" ;
	  id = IDENT ; b = [ "discriminated" -> true | -> false ] ->
	    VernacCreateHintDb (id, b)
      | IDENT "Remove"; IDENT "Hints"; ids = LIST1 global; dbnames = opt_hintbases ->
	  VernacRemoveHints (dbnames, ids)
      | IDENT "Hint"; local = obsolete_locality; h = hint;
	  dbnames = opt_hintbases ->
	  VernacHints (local,dbnames, h)
      (* Declare "Resolve" explicitly so as to be able to later extend with
         "Resolve ->" and "Resolve <-" *)
      | IDENT "Hint"; IDENT "Resolve"; lc = LIST1 reference_or_constr; 
	info = hint_info; dbnames = opt_hintbases ->
	  VernacHints (false,dbnames,
	    HintsResolve (List.map (fun x -> (info, true, x)) lc))
      ] ];
  obsolete_locality:
    [ [ IDENT "Local" -> true | -> false ] ]
  ;
  reference_or_constr:
   [ [ r = global -> HintsReference r
     | c = constr -> HintsConstr c ] ]
  ;
  hint:
    [ [ IDENT "Resolve"; lc = LIST1 reference_or_constr; info = hint_info ->
          HintsResolve (List.map (fun x -> (info, true, x)) lc)
      | IDENT "Immediate"; lc = LIST1 reference_or_constr -> HintsImmediate lc
      | IDENT "Transparent"; lc = LIST1 global -> HintsTransparency (lc, true)
      | IDENT "Opaque"; lc = LIST1 global -> HintsTransparency (lc, false)
      | IDENT "Mode"; l = global; m = mode -> HintsMode (l, m)
      | IDENT "Unfold"; lqid = LIST1 global -> HintsUnfold lqid
      | IDENT "Constructors"; lc = LIST1 global -> HintsConstructors lc ] ]
    ;
  constr_body:
    [ [ ":="; c = lconstr -> c
      | ":"; t = lconstr; ":="; c = lconstr -> CAst.make ~loc:!@loc @@ CCast(c,CastConv t) ] ]
  ;
  mode:
    [ [ l = LIST1 [ "+" -> ModeInput
                  | "!" -> ModeNoHeadEvar
                  | "-" -> ModeOutput ] -> l ] ]
  ;
END
