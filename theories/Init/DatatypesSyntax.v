(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Datatypes.

(** Symbolic notations for things in [Datatypes.v] *)

Infix LEFTA 4 "+" sum.
Infix LEFTA 3 "*" prod.
Notation "( x , y )" := (pair ? ? x y) (at level 0).
Notation Fst := (fst ? ?).
Notation Snd := (snd ? ?).

(** Parsing only of things in [Datatypes.v] *)

Notation "< A , B > ( x , y )" := (pair A B x y) (at level 0, only parsing).
Notation "< A , B > 'Fst' ( p )" := (fst A B p) (at level 1, only parsing).
Notation "< A , B > 'Snd' ( p )" := (snd A B p) (at level 1, only parsing).

