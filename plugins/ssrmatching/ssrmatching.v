(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)

Declare ML Module "ssrmatching_plugin".

(**
 This file is the Gallina part of the ssreflect matching implementation.

 In particular, it defines:

        nomatch T t == t, but the first two arguments T and t
                       of this transparent identity function are ignored
                       by the ssreflect matching algorithm.                  **)

(* Definition used in the implementatin of the under tactic,
   see also coq/coq#11118 *)
Definition nomatch T (t : T) := t.
Register nomatch as plugins.ssrmatching.nomatch.

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
Notation "( X 'in' t )" := (_ : fun X => t) : ssrpatternscope.

(* Some shortcuts for recurrent "X in t" parts.                               *)
Notation RHS := (X in _ = X)%pattern.
Notation LHS := (X in X = _)%pattern.

End SsrMatchingSyntax.

Export SsrMatchingSyntax.

Tactic Notation "ssrpattern" ssrpatternarg(p) := ssrpattern p .
