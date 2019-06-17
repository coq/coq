(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Mod_subst
open Tac2expr

val intern : strict:bool -> raw_tacexpr -> glb_tacexpr * type_scheme
val intern_typedef : (KerName.t * int) Id.Map.t -> raw_quant_typedef -> glb_quant_typedef
val intern_open_type : raw_typexpr -> type_scheme

(** Check that a term is a value. Only values are safe to marshall between
    processes. *)
val is_value : glb_tacexpr -> bool
val check_unit : ?loc:Loc.t -> type_scheme -> unit

val check_subtype : type_scheme -> type_scheme -> bool
(** [check_subtype t1 t2] returns [true] iff all values of instances of type [t1]
    also have type [t2]. *)

val subst_type : substitution -> 'a glb_typexpr -> 'a glb_typexpr
val subst_expr : substitution -> glb_tacexpr -> glb_tacexpr
val subst_quant_typedef : substitution -> glb_quant_typedef -> glb_quant_typedef
val subst_type_scheme : substitution -> type_scheme -> type_scheme

val subst_rawexpr : substitution -> raw_tacexpr -> raw_tacexpr

(** {5 Notations} *)

val globalize : Id.Set.t -> raw_tacexpr -> raw_tacexpr
(** Replaces all qualified identifiers by their corresponding kernel name. The
    set represents bound variables in the context. *)

(** Errors *)

val error_nargs_mismatch : ?loc:Loc.t -> ltac_constructor -> int -> int -> 'a
val error_nparams_mismatch : ?loc:Loc.t -> int -> int -> 'a

(** Misc *)

val drop_ltac2_env : Genintern.Store.t -> Genintern.Store.t
