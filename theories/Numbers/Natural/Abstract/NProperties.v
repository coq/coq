(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export NAxioms NMaxMin.

(** This functor summarizes all known facts about N.
    For the moment it is only an alias to the last functor which
    subsumes all others.
*)

Module Type NPropSig := NMaxMinProp.

Module NPropFunct (N:NAxiomsSig) <: NPropSig N.
 Include NPropSig N.
End NPropFunct.
