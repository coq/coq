(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init Std.

Ltac2 @ external get : ident list -> Std.reference option := "rocq-runtime.plugins.ltac2" "env_get".
(** Returns the global reference corresponding to the absolute name given as
    argument if it exists. *)

Ltac2 @ external expand : ident list -> Std.reference list := "rocq-runtime.plugins.ltac2" "env_expand".
(** Returns the list of all global references whose absolute name contains
    the argument list as a suffix. *)

Ltac2 @ external path : Std.reference -> ident list := "rocq-runtime.plugins.ltac2" "env_path".
(** Returns the absolute name of the given reference. Panics if the reference
    does not exist. *)

Ltac2 @ external instantiate : Std.reference -> constr := "rocq-runtime.plugins.ltac2" "env_instantiate".
(** Returns a fresh instance of the corresponding reference, in particular
    generating fresh universe variables and constraints when this reference is
    universe-polymorphic. *)
