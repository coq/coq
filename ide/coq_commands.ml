(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

let commands = [
  [(* "Abort"; *)
   "Add Abstract Ring A Aplus Amult Aone Azero Ainv Aeq T.";
   "Add Abstract Semi Ring A Aplus Amult Aone Azero Aeq T.";
   "Add Field";
   "Add LoadPath";
   "Add ML Path";
   "Add Morphism";
   "Add Printing If";
   "Add Printing Let";
   "Add Rec LoadPath";
   "Add Rec ML Path";
   "Add Ring A Aplus Amult Aone Azero Ainv Aeq T [ c1 ... cn ]. ";
   "Add Semi Ring A Aplus Amult Aone Azero Aeq T [ c1 ... cn ].";
   "Add Setoid";
   "Axiom";];
  [(* "Back"; *) ];
  ["Canonical Structure";
   (* "Cd"; *)
   "Chapter";
   (* "Check"; *)
   "Coercion";
   "Coercion Local";
   "CoFixpoint";
   "CoInductive";
   (* "Correctness"; *)];
  ["Declare ML Module";
   "Defined.";
   "Definition";
   "Derive Dependent Inversion";
   "Derive Dependent Inversion__clear";
   "Derive Inversion";
   "Derive Inversion__clear";
   (* "Drop"; *)];
  ["End";
   "End Silent.";
   "Eval"; 
   "Extract Constant";
   "Extract Inductive";
   "Extraction";
   "Extraction Inline";
   "Extraction Language";
   "Extraction Module";
   "Extraction NoInline";];
  ["Fact";
   "Fixpoint";
   "Focus";];
  ["Global Variable";
   "Goal";
   "Grammar";];
  ["Hint";
   "Hint Constructors";
   "Hint Extern";
   "Hint Immediate";
   "Hint Resolve";
   "Hint Rewrite";
   "Hint Unfold";
   "Hypothesis";];
  ["Identity Coercion";
   "Implicits";
   "Inductive";
   "Infix";
   (* "Inspect"; *)];
  ["Lemma";
   "Load";
   "Load Verbose";
   "Local";
   (*
    "Locate";
   "Locate File";
   "Locate Library"; *)];
  ["Module";
   "Module Type";
   "Mutual Inductive";];
  ["Notation";];
  ["Opaque";];
  ["Parameter";
   (*"Print";
   "Print All";
   "Print Classes";
   "Print Coercion Paths";
   "Print Coercions";
   "Print Extraction Inline";
   "Print Graph";
   "Print Hint";
   "Print HintDb";
   "Print LoadPath";
   "Print ML Modules";
   "Print ML Path";
   "Print Module";
   "Print Module Type";
   "Print Modules";
   "Print Proof";
   "Print Section";
   "Print Table Printing If";
   "Print Table Printing Let";*)
   "Proof.";
   (*"Pwd";*)];
  ["Qed.";
   (* "Quit";*)];
  ["Read Module";
   "Record";
   "Recursive Extraction";
   "Recursive Extraction Module";
   "Remark";
   "Remove LoadPath";
   "Remove Printing If";
   "Remove Printing Let";
   "Require";
   "Require Export";
   "Require Import";
   (* "Reset"; *)
   "Reset Extraction Inline";
   (* "Reset Initial"; *)
   (* "Restart"; *)
   "Restore State"; 
   (* "Resume"; *)];
  [  "Save.";
     "Scheme";
     (*"Search";
     "Search ... inside ...";
     "Search ... outside ...";
     "SearchAbout";
     "SearchPattern";
     "SearchPattern ... inside ...";
     "SearchPattern ... outside ...";
     "SearchRewrite";
     "SearchRewrite ... inside ...";
     "SearchRewrite ... outside ..."; *)
     "Section";
     "Set Extraction AutoInline";
     "Set Extraction Optimize";
     "Set Hyps__limit";
     "Set Implicit Arguments";
     "Set Printing Coercion";
     "Set Printing Coercions";
     "Set Printing Synth";
     "Set Printing Wildcard";
     "Set Silent.";
     "Set Undo";
     (*"Show";
     "Show Conjectures";
     "Show Implicits";
     "Show Intro";
     "Show Intros";
     "Show Programs";
     "Show Proof";
     "Show Script";
     "Show Tree";*)
     "Structure";
     (* "Suspend"; *)
     "Syntactic Definition";
     "Syntax";];
  ["Tactic Definition";
   "Test Printing If";
   "Test Printing Let";
   "Test Printing Synth";
   "Test Printing Wildcard";
   "Theorem";
   "Time";
   "Transparent";];
  [(* "Undo"; *)
   "Unfocus";
   "Unset Extraction AutoInline";
   "Unset Extraction Optimize";
   "Unset Hyps__limit";
   "Unset Implicit Arguments";
   "Unset Printing Coercion";
   "Unset Printing Coercions";
   "Unset Printing Synth";
   "Unset Printing Wildcard";
   "Unset Silent.";
   "Unset Undo";];
  ["Variable";
   "Variables";];
  ["Write State";];
]

let state_preserving = [
  "Check";
  "Eval";
  "Eval compute in";
  "Extraction";
  "Extraction Library";
  "Extraction Module";
  "Inspect";
  "Locate";
  "Print";
  "Print All.";
  "Print Classes";
  "Print Coercion Paths";
  "Print Coercions";
  "Print Extraction Inline";
  "Print Graph";
  "Print Hint";
  "Print HintDb";
  "Print LoadPath";
  "Print ML Modules";
  "Print ML Path";
  "Print Module";
  "Print Module Type";
  "Print Modules";
  "Print Proof";
  "Print Scope";
  "Print Scopes.";
  "Print Section";
  
  "Print Table Printing If";
  "Print Table Printing Let";

  "Print Visibility";

  "Pwd.";

  "Recursive Extraction";
  "Recursive Extraction Library";

  "Search";
  "SearchAbout";
  "SearchPattern";
  "SearchRewrite";

  "Show";
  "Show Conjectures";
  "Show Implicits";
  "Show Intro";
  "Show Intros";
  "Show Proof";
  "Show Script";
  "Show Tree";

  "Test Printing If";
  "Test Printing Let";
  "Test Printing Synth";
  "Test Printing Wildcard";
]


let tactics = 
  [
    [
      "abstract";
      "absurd";
      "apply";
      "apply __ with";
      "assert";
      "assumption.";
      "auto.";
      "auto with";
      "autorewrite";
    ];

   [
     "case";
     "case __ with";
     "cbv";
     "change";
     "change __ in";
     "clear";
     "clearbody";
     "compare";
     "compute";
     "congruence";
     "constructor";
     "constructor __ with";
     "contradiction.";
     "cut";
     "cutrewrite";
   ];

   [
     "decide equality.";
     "decompose";
     "decompose record";
     "decompose sum";
     "dependent inversion";
     "dependent inversion __ with";
     "dependent inversion__clear";
     "dependent inversion__clear __ with";
     "dependent rewrite ->";
     "dependent rewrite <-";
     "destruct";
     "discriminate.";
     "discriminate";
     "discrR.";
     "do";
     "double induction";
   ];

   [
     "eapply";
     "eauto.";
     "eauto with";
     "elim";
     "elim __ using";
     "elim __ with";
     "elimtype";
     "exact";
     "exists";
   ];

   [
     "fail.";
     "field.";
     "first";
     "firstorder.";
     "firstorder";
     "firstorder using";
     "firstorder with";
     "fold";
     "fourier.";
     "functional induction";
   ];

   [
     "generalize";
     "generalize dependent";
   ];
   
   [
     "hnf";
   ];

   [
     "idtac.";
     "induction";
     "info";
     "injection";
     "intro";
     "intro after";
     "intro __ after";
     "intros";
     "intros.";
     "intros";
     "intros <pattern> ";
     "intros until";
     "intuition.";
     "intuition";
     "inversion";
     "inversion __ in";
     "inversion __ using";
     "inversion __ using __ in";
     "inversion__clear";
     "inversion__clear __ in";
   ];

   [
     "jp <n>";
     "jp.";
   ];

   [
     "lapply";
     "lazy";
     "left";
   ];

   [
     "move __ after";
   ];

   [
     "omega";
   ];

   [
     "pattern";
     "pose";
     "progress";
   ];

   [
     "quote";
   ];

   [
     "red.";
     "red in";
     "refine";
     "reflexivity.";
     "rename __ into";
     "repeat";
     "replace __ with";
     "rewrite";
     "rewrite __ in";
     "rewrite ->";
     "rewrite -> __ in";
     "rewrite <-";
     "rewrite <- __ in";
     "right.";
     "ring.";
   ];

   [
     "set";
     "setoid__replace";
     "setoid__rewrite";
     "simpl.";
     "simpl __ in";
     "simple destruct";
     "simple induction";
     "simple inversion";
     "simplify__eq";
     "solve";
     "split.";
     "split__Rabs.";
     "split__Rmult.";
     "subst";
     "symmetry.";
   ];

   [
     "tauto.";
     "transitivity";
     "trivial.";
     "try";
   ];
   
   [
     "unfold";
     "unfold __ in";
   ];
]


