(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pcoq
open Pp
open Tactic
open Util
open Vernac_
open Topconstr
open Vernacexpr
open Prim
open Constr

let thm_token = G_vernacnew.thm_token

(* Proof commands *)
GEXTEND Gram
  GLOBAL: command;

  destruct_location :
  [ [ IDENT "Conclusion"  -> Tacexpr.ConclLocation ()
    | discard = [ IDENT "Discardable" -> true | -> false ]; IDENT "Hypothesis"
	-> Tacexpr.HypLocation discard ] ]
  ;
  opt_hintbases:
  [ [ -> []
    | ":"; l = LIST1 IDENT -> l ] ]
  ;
  command:
    [ [ IDENT "Goal"; c = Constr.lconstr -> VernacGoal c
      | IDENT "Proof" -> VernacNop
      | IDENT "Proof"; "with"; ta = tactic -> VernacProof ta
      | IDENT "Abort" -> VernacAbort None
      | IDENT "Abort"; IDENT "All" -> VernacAbortAll
      | IDENT "Abort"; id = identref -> VernacAbort (Some id)
      | IDENT "Existential"; n = natural; c = constr_body ->
	  VernacSolveExistential (n,c)
      | IDENT "Qed" -> VernacEndProof (true,None)
      | IDENT "Save" -> VernacEndProof (true,None)
      | IDENT "Save"; tok = thm_token; id = base_ident ->
	  VernacEndProof (true,Some (id,Some tok))
      | IDENT "Save"; id = base_ident -> VernacEndProof (true,Some (id,None))
      | IDENT "Defined" -> VernacEndProof (false,None)
      |	IDENT "Defined"; id=base_ident -> VernacEndProof (false,Some (id,None))
      | IDENT "Suspend" -> VernacSuspend
      | IDENT "Resume" -> VernacResume None
      | IDENT "Resume"; id = identref -> VernacResume (Some id)
      | IDENT "Restart" -> VernacRestart
      | IDENT "Proof"; c = Constr.lconstr -> VernacExactProof c
      | IDENT "Undo" -> VernacUndo 1
      | IDENT "Undo"; n = natural -> VernacUndo n
      | IDENT "Focus" -> VernacFocus None
      | IDENT "Focus"; n = natural -> VernacFocus (Some n)
      | IDENT "Unfocus" -> VernacUnfocus
      | IDENT "Show" -> VernacShow (ShowGoal None)
      | IDENT "Show"; n = natural -> VernacShow (ShowGoal (Some n))
      | IDENT "Show"; IDENT "Implicits"; n = natural ->
	  VernacShow (ShowGoalImplicitly (Some n))
      | IDENT "Show"; IDENT "Implicits" -> VernacShow (ShowGoalImplicitly None)
      | IDENT "Show"; IDENT "Node" -> VernacShow ShowNode
      | IDENT "Show"; IDENT "Script" -> VernacShow ShowScript
      | IDENT "Show"; IDENT "Existentials" -> VernacShow ShowExistentials
      | IDENT "Show"; IDENT "Tree" -> VernacShow ShowTree
      | IDENT "Show"; IDENT "Conjectures" -> VernacShow ShowProofNames
      | IDENT "Show"; IDENT "Proof" -> VernacShow ShowProof
      | IDENT "Show"; IDENT "Intro" -> VernacShow (ShowIntros false)
      | IDENT "Show"; IDENT "Intros" -> VernacShow (ShowIntros true)
      | IDENT "Explain"; IDENT "Proof"; l = LIST0 integer ->
	  VernacShow (ExplainProof l)
      | IDENT "Explain"; IDENT "Proof"; IDENT "Tree"; l = LIST0 integer -> 
	  VernacShow (ExplainTree l)
      | IDENT "Go"; n = natural -> VernacGo (GoTo n)
      | IDENT "Go"; IDENT "top" -> VernacGo GoTop
      | IDENT "Go"; IDENT "prev" -> VernacGo GoPrev
      | IDENT "Go"; IDENT "next" -> VernacGo GoNext
      | IDENT "Guarded" -> VernacCheckGuard
(* Hints for Auto and EAuto *)

      | IDENT "HintDestruct"; 
	  local = locality;
          dloc = destruct_location;
          id  = base_ident;
          hyptyp = Constr.constr_pattern;
          pri = natural;
          "["; tac = tactic; "]" -> 
	    VernacHintDestruct (id,dloc,hyptyp,pri,tac)

      | IDENT "Hint"; local = locality; hintname = base_ident; 
	  dbnames = opt_hintbases; ":="; h = hint ->
            VernacHints (dbnames, h hintname)
	  
      | IDENT "Hints"; local = locality; (dbnames,h) = hints ->
	  VernacHints (dbnames, h)
	  

(*This entry is not commented, only for debug*)
      | IDENT "PrintConstr"; c = Constr.constr -> 
	  VernacExtend ("PrintConstr",
	    [Genarg.in_gen Genarg.rawwit_constr c])
      ] ];

  hint:
    [ [ IDENT "Resolve"; c = Constr.constr -> fun name -> HintsResolve [Some name, c]
      | IDENT "Immediate"; c = Constr.constr -> fun name -> HintsImmediate [Some name, c]
      | IDENT "Unfold"; qid = global -> fun name -> HintsUnfold [Some name,qid]
      | IDENT "Constructors"; c = global -> fun n -> HintsConstructors (n,c)
      | IDENT "Extern"; n = natural; c = Constr.constr ; tac = tactic ->
	  fun name -> HintsExtern (name,n,c,tac) ] ]
  ;
  hints:
    [ [ IDENT "Resolve"; l = LIST1 global; dbnames = opt_hintbases ->
         (dbnames, HintsResolve (List.map (fun qid -> (None, CRef qid)) l))
      | IDENT "Immediate"; l = LIST1 global; dbnames = opt_hintbases ->
        (dbnames, HintsImmediate (List.map (fun qid -> (None, CRef qid)) l))
      | IDENT "Unfold"; l = LIST1 global; dbnames = opt_hintbases ->
        (dbnames, HintsUnfold (List.map (fun qid -> (None,qid)) l)) ] ]
    ;
  constr_body:
    [ [ ":="; c = lconstr -> c
      | ":"; t = lconstr; ":="; c = lconstr -> CCast(loc,c,t) ] ]
  ;
END
