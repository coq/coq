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

Arguments Scope sum [type_scope type_scope].
Arguments Scope prod [type_scope type_scope].

Infix LEFTA 4 "+" sum : type_scope.
Notation "x * y" := (prod x y) (at level 3, right associativity) : type_scope
  V8only (at level 30, left associativity).

Notation "( x , y )" := (pair ? ? x y) (at level 0)
  V8only "x , y" (at level 150, left associativity).
Notation Fst := (fst ? ?).
Notation Snd := (snd ? ?).

Arguments Scope option [ type_scope ].

(** Parsing only of things in [Datatypes.v] *)

V7only[
Notation "< A , B > ( x , y )" := (pair A B x y) (at level 1, only parsing, A annot).
Notation "< A , B > 'Fst' ( p )" := (fst A B p) (at level 1, only parsing, A annot).
Notation "< A , B > 'Snd' ( p )" := (snd A B p) (at level 1, only parsing, A annot).
].
