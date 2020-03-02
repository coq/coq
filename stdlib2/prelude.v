(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* We activate implicit arguments by default *)
Export Set Implicit Arguments.
Export Unset Strict Implicit.
Export Unset Printing Implicit Defensive.
Export Set Primitive Projections.
Export Unset Auto Template Polymorphism.
Export Set Loose Hint Behavior "Strict".

(** Enable proof mode. *)
Declare ML Module "ltac_plugin".
Global Set Default Proof Mode "Classic".

(** Scopes *)

Declare Scope type_scope.
Delimit Scope type_scope with type.
Declare Scope function_scope.
Delimit Scope function_scope with function.
Declare Scope core_scope.
Delimit Scope core_scope with core.

Bind Scope type_scope with Sortclass.
Bind Scope function_scope with Funclass.

Open Scope core_scope.
Open Scope function_scope.
Open Scope type_scope.

(** Notations available initially *)
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ'  x  ..  y ']' ,  '/' t ']'").
