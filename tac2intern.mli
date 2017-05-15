(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Names
open Mod_subst
open Tac2expr

val loc_of_tacexpr : raw_tacexpr -> Loc.t

val intern : raw_tacexpr -> glb_tacexpr * type_scheme
val intern_typedef : (KerName.t * int) Id.Map.t -> raw_quant_typedef -> glb_quant_typedef
val intern_open_type : raw_typexpr -> type_scheme

(** Check that a term is a value. Only values are safe to marshall between
    processes. *)
val is_value : glb_tacexpr -> bool
val check_unit : ?loc:Loc.t -> int glb_typexpr -> unit

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

val error_nargs_mismatch : Loc.t -> int -> int -> 'a
val error_nparams_mismatch : Loc.t -> int -> int -> 'a
