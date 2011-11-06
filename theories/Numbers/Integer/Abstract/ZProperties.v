(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export ZAxioms ZMulOrder ZSgnAbs.

(** This functor summarizes all known facts about Z.
    For the moment it is only an alias to [ZMulOrderPropFunct], which
    subsumes all others, plus properties of [sgn] and [abs].
*)

Module Type ZPropSig (Z:ZAxiomsExtSig) :=
 ZMulOrderPropFunct Z <+ ZSgnAbsPropSig Z.

Module ZPropFunct (Z:ZAxiomsExtSig) <: ZPropSig Z.
 Include ZPropSig Z.
End ZPropFunct.

