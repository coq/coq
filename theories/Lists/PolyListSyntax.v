(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Syntax for list concatenation *)

Require PolyList.

V8Infix "::" cons (at level 45, right associativity) : list_scope.

Infix RIGHTA 7 "^" app : list_scope V8only RIGHTA 45 "++".

Open Scope list_scope.
