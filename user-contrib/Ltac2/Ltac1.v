(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module defines the Ltac2 FFI to Ltac1 code. Due to intricate semantics
    of the latter, the functions described here are voluntarily under-specified.
    Not for the casual user, handle with care and expect undefined behaviours
    otherwise. **)

Require Import Ltac2.Init.

Ltac2 Type t.
(** Dynamically-typed Ltac1 values. *)

Ltac2 @ external ref : ident list -> t := "ltac2" "ltac1_ref".
(** Returns the Ltac1 definition with the given absolute name. *)

Ltac2 @ external run : t -> unit := "ltac2" "ltac1_run".
(** Runs an Ltac1 value, assuming it is a 'tactic', i.e. not returning
    anything. *)

Ltac2 @ external lambda : (t -> t) -> t := "ltac2" "ltac1_lambda".
(** Embed an Ltac2 function into Ltac1 values. Contrarily to the ltac1:(...)
    quotation, this function allows both to capture an Ltac2 context inside the
    closure and to return an Ltac1 value. Returning values in Ltac1 is a
    intrepid endeavour prone to weird runtime semantics. *)

Ltac2 @ external apply : t -> t list -> (t -> unit) -> unit := "ltac2" "ltac1_apply".
(** Applies an Ltac1 value to a list of arguments, and provides the result in
    CPS style. It does **not** run the returned value. *)

(** Conversion functions *)

Ltac2 @ external of_constr : constr -> t := "ltac2" "ltac1_of_constr".
Ltac2 @ external to_constr : t -> constr option := "ltac2" "ltac1_to_constr".

Ltac2 @ external of_ident : ident -> t := "ltac2" "ltac1_of_ident".
Ltac2 @ external to_ident : t -> ident option := "ltac2" "ltac1_to_ident".

Ltac2 @ external of_list : t list -> t := "ltac2" "ltac1_of_list".
Ltac2 @ external to_list : t -> t list option := "ltac2" "ltac1_to_list".
