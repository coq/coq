(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

let thm_token = Gram.Entry.create "vernac:thm_token"

(* Proof commands *)
if !Options.v7 then
GEXTEND Gram
  GLOBAL: command;

  destruct_location :
  [ [ IDENT "Conclusion"  -> Tacexpr.ConclLocation ()
    | discard = [ IDENT "Discardable" -> true | -> false ]; "Hypothesis"
	-> Tacexpr.HypLocation discard ] ]
  ;
  opt_hintbases:
  [ [ -> []
    | ":"; l = LIST1 IDENT -> l ] ]
  ;
  command:
    [ [ IDENT "Goal"; c = Constr.constr -> VernacGoal c
      | "Proof" -> VernacProof (Tacexpr.TacId "")
      | "Proof"; "with"; ta = tactic -> VernacProof ta
      | IDENT "Abort" -> VernacAbort None
      | IDENT "Abort"; IDENT "All" -> VernacAbortAll
      | IDENT "Abort"; id = identref -> VernacAbort (Some id)
      | IDENT "Admitted" -> VernacEndProof Admitted
      | "Qed" -> VernacEndProof (Proved (true,None))
      | IDENT "Save" -> VernacEndProof (Proved (true,None))
      | IDENT "Defined" -> VernacEndProof (Proved (false,None))
      |	IDENT "Defined"; id=identref -> 
	  VernacEndProof (Proved (false,Some (id,None)))
      | IDENT "Save"; tok = thm_token; id = identref ->
	  VernacEndProof (Proved (true,Some (id,Some tok)))
      | IDENT "Save"; id = identref ->
	  VernacEndProof (Proved (true,Some (id,None)))
      | IDENT "Suspend" -> VernacSuspend
      | IDENT "Resume" -> VernacResume None
      | IDENT "Resume"; id = identref -> VernacResume (Some id)
      | IDENT "Restart" -> VernacRestart
      | "Proof"; c = Constr.constr -> VernacExactProof c
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
      | IDENT "Show"; "Proof" -> VernacShow ShowProof
      | IDENT "Show"; IDENT "Intro" -> VernacShow (ShowIntros false)
      | IDENT "Show"; IDENT "Intros" -> VernacShow (ShowIntros true)
      | IDENT "Explain"; "Proof"; l = LIST0 integer ->
	  VernacShow (ExplainProof l)
      | IDENT "Explain"; "Proof"; IDENT "Tree"; l = LIST0 integer -> 
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
	    VernacHints(local,[],HintsDestruct (id,pri,dloc,hyptyp,tac))

      | IDENT "Hint"; local = locality; hintname = base_ident; 
	  dbnames = opt_hintbases; ":="; h = hint
          -> VernacHints (local,dbnames, h hintname)
	  
      | IDENT "Hints"; local = locality; 
	  (dbnames,h) = hints -> VernacHints (local,dbnames, h)
	  

(*This entry is not commented, only for debug*)
      | IDENT "PrintConstr"; c = Constr.constr -> 
	  VernacExtend ("PrintConstr",
	    [Genarg.in_gen Genarg.rawwit_constr c])
      ] ];

  locality:
    [ [ IDENT "Local" -> true | -> false ] ]
  ;
  hint:
    [ [ IDENT "Resolve"; c = Constr.constr -> fun name -> HintsResolve [Some name, c]
      | IDENT "Immediate"; c = Constr.constr -> fun name -> HintsImmediate [Some name, c]
      | IDENT "Unfold"; qid = global -> fun name -> HintsUnfold [Some name,qid]
      | IDENT "Constructors"; c = global -> fun n ->
          HintsConstructors (Some n,[c])
      | IDENT "Extern"; n = natural; c = Constr.constr ; tac = tactic ->
	  fun name -> HintsExtern (Some name,n,c,tac) ] ]
  ;
  hints:
    [ [ IDENT "Resolve"; l = LIST1 global; dbnames = opt_hintbases ->
         (dbnames, 
	  HintsResolve
	    (List.map (fun qid -> (None, CAppExpl(loc,(None,qid),[]))) l))
      | IDENT "Immediate"; l = LIST1 global; dbnames = opt_hintbases ->
        (dbnames, 
	 HintsImmediate
	   (List.map (fun qid-> (None, CAppExpl (loc,(None,qid),[]))) l))
      | IDENT "Unfold"; l = LIST1 global; dbnames = opt_hintbases ->
        (dbnames, HintsUnfold (List.map (fun qid -> (None,qid)) l)) ] ]
    ;
  END
