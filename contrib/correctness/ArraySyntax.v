(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Syntax and pretty-print for arrays *)

Require Arrays.

Grammar constr constr0 :=
  array_access
    [ "#" ident($t) "[" constr($c) "]" ] -> [ (access $t $c) ].

Syntax constr level 0 :
  array_access
    [ << (access ($VAR $t) $c) >> ] -> [ "#" $t "[" $c:L "]" ].
