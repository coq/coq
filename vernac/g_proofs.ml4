(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Glob_term
open Constrexpr
open Vernacexpr
open Proof_global

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_

let thm_token = G_vernac.thm_token

let hint = Gram.entry_create "hint"

let warn_deprecated_focus =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
         (fun () ->
           Pp.strbrk
             "The Focus command is deprecated; use bullets or focusing brackets instead"
         )

let warn_deprecated_focus_n n =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
         (fun () ->
           Pp.(str "The Focus command is deprecated;" ++ spc ()
               ++ str "use '" ++ int n ++ str ": {' instead")
         )

let warn_deprecated_unfocus =
  CWarnings.create ~name:"deprecated-unfocus" ~category:"deprecated"
         (fun () -> Pp.strbrk "The Unfocus command is deprecated")

(* Proof commands *)
GEXTEND Gram
  GLOBAL: hint command;

  opt_hintbases:
  [ [ -> []
    | ":"; l = LIST1 [id = IDENT -> id ] -> l ] ]
  ;
  command:
    [ [ IDENT "Goal"; c = lconstr ->
        VernacDefinition (Decl_kinds.(NoDischarge, Definition), ((CAst.make ~loc:!@loc Names.Anonymous), None), ProveBody ([], c))
      | IDENT "Proof" -> VernacProof (None,None)
      | IDENT "Proof" ; IDENT "Mode" ; mn = string -> VernacProofMode mn
      | IDENT "Proof"; c = lconstr -> VernacExactProof c
      | IDENT "Abort" -> VernacAbort None
      | IDENT "Abort"; IDENT "All" -> VernacAbortAll
      | IDENT "Abort"; id = identref -> VernacAbort (Some id)
      | IDENT "Existential"; n = natural; c = constr_body ->
	  VernacSolveExistential (n,c)
      | IDENT "Admitted" -> VernacEndProof Admitted
      | IDENT "Qed" -> VernacEndProof (Proved (Opaque,None))
      | IDENT "Save"; id = identref ->
	  VernacEndProof (Proved (Opaque, Some id))
      | IDENT "Defined" -> VernacEndProof (Proved (Transparent,None))
      |	IDENT "Defined"; id=identref ->
	  VernacEndProof (Proved (Transparent,Some id))
      | IDENT "Restart" -> VernacRestart
      | IDENT "Undo" -> VernacUndo 1
      | IDENT "Undo"; n = natural -> VernacUndo n
      | IDENT "Undo"; IDENT "To"; n = natural -> VernacUndoTo n
      | IDENT "Focus" ->
         warn_deprecated_focus ~loc:!@loc ();
         VernacFocus None
      | IDENT "Focus"; n = natural ->
         warn_deprecated_focus_n n ~loc:!@loc ();
         VernacFocus (Some n)
      | IDENT "Unfocus" ->
         warn_deprecated_unfocus ~loc:!@loc ();
         VernacUnfocus
      | IDENT "Unfocused" -> VernacUnfocused
      | IDENT "Show" -> VernacShow (ShowGoal OpenSubgoals)
      | IDENT "Show"; n = natural -> VernacShow (ShowGoal (NthGoal n))
      | IDENT "Show"; id = ident -> VernacShow (ShowGoal (GoalId id))
      | IDENT "Show"; IDENT "Script" -> VernacShow ShowScript
      | IDENT "Show"; IDENT "Existentials" -> VernacShow ShowExistentials
      | IDENT "Show"; IDENT "Universes" -> VernacShow ShowUniverses
      | IDENT "Show"; IDENT "Conjectures" -> VernacShow ShowProofNames
      | IDENT "Show"; IDENT "Proof" -> VernacShow ShowProof
      | IDENT "Show"; IDENT "Intro" -> VernacShow (ShowIntros false)
      | IDENT "Show"; IDENT "Intros" -> VernacShow (ShowIntros true)
      | IDENT "Show"; IDENT "Match"; id = reference -> VernacShow (ShowMatch id)
      | IDENT "Guarded" -> VernacCheckGuard
      (* Hints for Auto and EAuto *)
      | IDENT "Create"; IDENT "HintDb" ;
	  id = IDENT ; b = [ "discriminated" -> true | -> false ] ->
	    VernacCreateHintDb (id, b)
      | IDENT "Remove"; IDENT "Hints"; ids = LIST1 global; dbnames = opt_hintbases ->
	  VernacRemoveHints (dbnames, ids)
      | IDENT "Hint"; h = hint; dbnames = opt_hintbases ->
          VernacHints (dbnames, h)
      ] ];
  reference_or_constr:
   [ [ r = global -> HintsReference r
     | c = constr -> HintsConstr c ] ]
  ;
  hint:
    [ [ IDENT "Resolve"; lc = LIST1 reference_or_constr; info = hint_info ->
          HintsResolve (List.map (fun x -> (info, true, x)) lc)
      | IDENT "Resolve"; "->"; lc = LIST1 global; n = OPT natural ->
          HintsResolveIFF (true, lc, n)
      | IDENT "Resolve"; "<-"; lc = LIST1 global; n = OPT natural ->
          HintsResolveIFF (false, lc, n)
      | IDENT "Immediate"; lc = LIST1 reference_or_constr -> HintsImmediate lc
      | IDENT "Variables"; IDENT "Transparent" -> HintsTransparency (HintsVariables, true)
      | IDENT "Variables"; IDENT "Opaque" -> HintsTransparency (HintsVariables, false)
      | IDENT "Constants"; IDENT "Transparent" -> HintsTransparency (HintsConstants, true)
      | IDENT "Constants"; IDENT "Opaque" -> HintsTransparency (HintsConstants, false)
      | IDENT "Transparent"; lc = LIST1 global -> HintsTransparency (HintsReferences lc, true)
      | IDENT "Opaque"; lc = LIST1 global -> HintsTransparency (HintsReferences lc, false)
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
