(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export ZAxioms ZMaxMin ZSgnAbs.

(** This functor summarizes all known facts about Z.
    For the moment it is only an alias to the last functor which
    subsumes all others, plus properties of [sgn] and [abs].
*)

Module Type ZPropSig (Z:ZAxiomsExtSig) :=
 ZMaxMinProp Z <+ ZSgnAbsPropSig Z.

Module ZPropFunct (Z:ZAxiomsExtSig) <: ZPropSig Z.
 Include ZPropSig Z.
End ZPropFunct.

