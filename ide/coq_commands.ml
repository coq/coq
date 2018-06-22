(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
   "Add LoadPath";
   "Add ML Path";
   "Add Morphism";
   "Add Printing Constructor";
   "Add Printing If";
   "Add Printing Let";
   "Add Printing Record";
   "Add Rec LoadPath";
   "Add Rec ML Path";
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
   "Variant";
   "Remark";
   "Remove LoadPath";
   "Remove Printing Constructor";
   "Remove Printing If";
   "Remove Printing Let";
   "Remove Printing Record";
   "Require";
   "Require Export";
   "Require Import";
   "Reset Extraction Inline";
   "Restore State";
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
     "Show Script";
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
   "Variables";];
  ["Write State";];
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
  "Print Modules";
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
  "SearchAbout (* deprecated *)";
  "SearchHead";
  "SearchPattern";
  "SearchRewrite";

  "Show";
  "Show Conjectures";
  "Show Existentials";
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
      "assert (__:__)";
      "assert (__:=__)";
      "assumption";
      "auto";
      "auto with";
      "autorewrite";
    ];

   [
     "case";
     "case __ with";
     "casetype";
     "cbv";
     "cbv in";
     "change";
     "change __ in";
     "clear";
     "clearbody";
     "cofix";
     "compare";
     "compute";
     "compute in";
     "congruence";
     "constructor";
     "constructor __ with";
     "contradiction";
     "cut";
     "cutrewrite";
   ];

   [
     "decide equality";
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
     "discriminate";
     "do";
     "double induction";
   ];

   [
     "eapply";
     "eauto";
     "eauto with";
     "eexact";
     "elim";
     "elim __ using";
     "elim __ with";
     "elimtype";
     "exact";
     "exists";
   ];

   [
     "fail";
     "field";
     "first";
     "firstorder";
     "firstorder using";
     "firstorder with";
     "fix";
     "fix __ with";
     "fold";
     "fold __ in";
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
     "idtac";
     "induction";
     "info";
     "injection";
     "instantiate (__:=__)";
     "intro";
     "intro after";
     "intro __ after";
     "intros";
     "intros until";
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
     "jp";
   ];

   [
     "lapply";
     "lazy";
     "lazy in";
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
     "pose __:=__)";
     "progress";
   ];

   [
     "quote";
   ];

   [
     "red";
     "red in";
     "refine";
     "reflexivity";
     "rename __ into";
     "repeat";
     "replace __ with";
     "rewrite";
     "rewrite __ in";
     "rewrite <-";
     "rewrite <- __ in";
     "right";
     "ring";
   ];

   [
     "set";
     "set (__:=__)";
     "setoid__replace";
     "setoid__rewrite";
     "simpl";
     "simpl __ in";
     "simple destruct";
     "simple induction";
     "simple inversion";
     "simplify__eq";
     "solve";
     "split";
(*     "split__Rabs";
     "split__Rmult";
*)
     "subst";
     "symmetry";
     "symmetry in";
   ];

   [
     "tauto";
     "transitivity";
     "trivial";
     "try";
   ];

   [
     "unfold";
     "unfold __ in";
   ];
]


