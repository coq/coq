(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

Require Import Ltac2.Init Ltac2.Std Ltac2.Control.

Ltac2 Type t.
(** Dynamically-typed Ltac1 values. *)

Ltac2 @ external ref : ident list -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_ref".
(** Returns the Ltac1 definition with the given absolute name. *)

Ltac2 @ external run : t -> unit := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_run".
(** Runs an Ltac1 value, assuming it is a 'tactic', i.e. not returning
    anything. *)

Ltac2 @ external lambda : (t -> t) -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_lambda".
(** Embed an Ltac2 function into Ltac1 values. Contrarily to the ltac1:(...)
    quotation, this function allows both to capture an Ltac2 context inside the
    closure and to return an Ltac1 value. Returning values in Ltac1 is a
    intrepid endeavour prone to weird runtime semantics. *)

Ltac2 @ external apply : t -> t list -> (t -> unit) -> unit := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_apply".
(** Applies an Ltac1 value to a list of arguments, and provides the result in
    CPS style. It does **not** run the returned value. *)

(** Conversion functions *)

Ltac2 @ external of_int : int -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_of_int".
(** Converts an Ltac2 int into an Ltac1 value. *)
Ltac2 @ external to_int : t -> int option := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_to_int".
(** Converts an Ltac1 int into an Ltac2 value. *)

Ltac2 @ external of_constr : constr -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_of_constr".
(** Converts an Ltac2 constr into an Ltac1 value. *)
Ltac2 @ external to_constr : t -> constr option := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_to_constr".
(** Converts an Ltac1 constr (which includes terms created via open_constr) into an Ltac2 value. *)

(** [preterm] is called [uconstr] in Ltac1. *)
Ltac2 @ external of_preterm : preterm -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_of_preterm".
Ltac2 @ external to_preterm : t -> preterm option := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_to_preterm".

Ltac2 @ external of_ident : ident -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_of_ident".
Ltac2 @ external to_ident : t -> ident option := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_to_ident".

Ltac2 @ external of_list : t list -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_of_list".
Ltac2 @ external to_list : t -> t list option := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_to_list".

Ltac2 @ external of_intro_pattern : intro_pattern -> t := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_of_intro_pattern".
Ltac2 @ external to_intro_pattern : t -> intro_pattern option := "rocq-runtime.plugins.ltac2_ltac1" "ltac1_to_intro_pattern".

(** Debug information *)

Ltac2 @ external tag_name : t -> string :=  "rocq-runtime.plugins.ltac2_ltac1" "ltac1_tag_name".
(** Name of the ltac1 value class the argument belongs to. Should be
    used only for error printing, typically "expected a constr but got a $tag_name". *)
