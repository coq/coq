(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)

Declare ML Module "rocq-runtime.plugins.ssrmatching".

Module SsrMatchingSyntax.

(* Reserve the notation for rewrite patterns so that the user is not allowed  *)
(* to declare it at a different level.                                        *)
Reserved Notation "( a 'in' b )"        (at level 0).
Reserved Notation "( a 'as' b )"        (at level 0).
Reserved Notation "( a 'in' b 'in' c )" (at level 0).
Reserved Notation "( a 'as' b 'in' c )" (at level 0).

Declare Scope ssrpatternscope.
Delimit Scope ssrpatternscope with pattern.

(* Notation to define shortcuts for the "X in t" part of a pattern.           *)
Notation "( X 'in' t )" := (_ : fun X => t) (only parsing) : ssrpatternscope.

(* Some shortcuts for recurrent "X in t" parts.                               *)
Notation RHS := (X in _ = X)%pattern.
Notation LHS := (X in X = _)%pattern.

End SsrMatchingSyntax.

Export SsrMatchingSyntax.

Tactic Notation "ssrpattern" ssrpatternarg(p) := ssrpattern p .
