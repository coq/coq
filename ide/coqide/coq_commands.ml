(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let commands = [
  [(* "Abort"; *)
   "Add Abstract Ring A Aplus Amult Aone Azero Ainv Aeq T.";
   "Add Abstract Semi Ring A Aplus Amult Aone Azero Aeq T.";
   "Add Field";
   "Add Morphism";
   "Add Printing Constructor";
   "Add Printing If";
   "Add Printing Let";
   "Add Printing Record";
   "Add Ring A Aplus Amult Aone Azero Ainv Aeq T [ c1 ... cn ]. ";
   "Add Semi Ring A Aplus Amult Aone Azero Aeq T [ c1 ... cn ].";
   "Add Relation";
   "Add Setoid";
   "Axiom";];
  [(* "Back"; *) ];
  ["Canonical Structure";
   "Chapter";
   "Coercion";
   "Coercion Local";
   "CoFixpoint";
   "CoInductive";
  ];
  ["Declare ML Module";
   "Defined.";
   "Definition";
   "Derive Dependent Inversion";
   "Derive Dependent Inversion__clear";
   "Derive Inversion";
   "Derive Inversion__clear";
  ];
  ["End";
   "End Silent.";
   "Eval";
   "Extract Constant";
   "Extract Foreign Constant";
   "Extract Callback";
   "Extract Inductive";
   "Extraction Inline";
   "Extraction Language";
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
   "Implicit Arguments";
   "Inductive";
   "Infix";
   ];
  ["Lemma";
   "Load";
   "Load Verbose";
   "Local";
   "Ltac";
  ];
  ["Module";
   "Module Type";
   "Mutual Inductive";];
  ["Notation";
   "Next Obligation";];
  ["Opaque";
   "Obligations Tactic";];
  ["Parameter";
   "Proof.";
   "Program Definition";
   "Program Fixpoint";
   "Program Lemma";
   "Program Theorem";
  ];
  ["Qed.";
   ];
  ["Read Module";
   "Record";
   "Remark";
   "Remove Printing Constructor";
   "Remove Printing If";
   "Remove Printing Let";
   "Remove Printing Record";
   "Require";
   "Require Export";
   "Require Import";
   "Reset Extraction Inline";
(*   "Reset Extraction Foreign";*)
   "Reset Extraction Callback";
   ];
  [  "Scheme";
     "Section";
     "Set Extraction AutoInline";
     "Set Extraction Optimize";
     "Set Hyps__limit";
     "Set Implicit Arguments";
     (*"Set Printing Coercion";
     "Set Printing Coercions";
     "Set Printing Synth";*)
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
     "Show Tree";*)
     "Structure";
     "Syntactic Definition";
     "Syntax";];
  [
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
   (*
   "Unset Printing Coercion";
   "Unset Printing Coercions";
   "Unset Printing Synth"; *)
   "Unset Printing Wildcard";
   "Unset Silent.";
   "Unset Undo";];
  ["Variable";
   "Variant";
   "Variables";];
]

let state_preserving = [
  "About";
  "Check";
  "Eval";
  "Eval lazy in";
  "Eval vm_compute in";
  "Eval compute in";
  "Extraction";
  "Extraction Library";
  "Extraction Module";
  "Inspect";
  "Locate";

  "Obligations";
  "Print";
  "Print All.";
  "Print Classes";
  "Print Coercion Paths";
  "Print Coercions";
  "Print Extraction Inline";
  "Print Extraction External";
  "Print Extraction Callback";
  "Print Grammar";
  "Print Graph";
  "Print Hint";
  "Print Hint *";
  "Print HintDb";
  "Print Implicit";
  "Print LoadPath";
  "Print ML Modules";
  "Print ML Path";
  "Print Module";
  "Print Module Type";
  "Print Libraries";
  "Print Proof";
  "Print Rewrite HintDb";
  "Print Setoids";
  "Print Scope";
  "Print Scopes.";
  "Print Section";

  "Print Table Printing If.";
  "Print Table Printing Let.";
  "Print Tables.";
  "Print Term";

  "Print Visibility";

  "Pwd.";

  "Recursive Extraction";
  "Recursive Extraction Library";

  "Search";
  "SearchPattern";
  "SearchRewrite";

  "Show";
  "Show Conjectures";
  "Show Existentials";
  "Show Implicits";
  "Show Intro";
  "Show Intros";
  "Show Proof";
  "Show Tree";

  "Test Printing If";
  "Test Printing Let";
  "Test Printing Synth";
  "Test Printing Wildcard";

]
