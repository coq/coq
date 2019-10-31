(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

(** Compatibility layer for [under] and [setoid_rewrite].

 Note: this file does not require [ssreflect]; it is both required by
 [ssrsetoid] and required by [ssrunder].

 Redefine [Coq.Classes.RelationClasses.Reflexive] here, so that doing
 [Require Import ssreflect] does not [Require Import RelationClasses],
 and conversely. **)

Section Defs.
  Context {A : Type}.
  Class Reflexive (R : A -> A -> Prop) :=
    reflexivity : forall x : A, R x x.
End Defs.

Register Reflexive as plugins.ssreflect.reflexive_type.
Register reflexivity as plugins.ssreflect.reflexive_proof.

Instance eq_Reflexive {A : Type} : Reflexive (@eq A) := @eq_refl A.
Instance iff_Reflexive : Reflexive iff := iff_refl.
