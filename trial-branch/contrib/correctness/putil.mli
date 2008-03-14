(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Names
open Term
open Pmisc
open Ptype
open Past
open Penv

val is_mutable : 'a ml_type_v -> bool
val is_pure : 'a ml_type_v -> bool

val named_app : ('a -> 'b) -> 'a assertion -> 'b assertion
val pre_app : ('a -> 'b) -> 'a precondition -> 'b precondition
val post_app : ('a -> 'b) -> 'a postcondition -> 'b postcondition

val anonymous : 'a -> 'a assertion
val anonymous_pre : bool -> 'a -> 'a precondition
val out_post : 'a postcondition option -> 'a
val pre_of_assert : bool -> 'a assertion -> 'a precondition
val assert_of_pre : 'a precondition -> 'a assertion

val force_post_name : 'a postcondition option -> 'a postcondition option
val force_bool_name : 'a postcondition option -> 'a postcondition option

val make_before_after : constr -> constr

val traverse_binders : local_env -> (type_v binder) list -> local_env
val initial_renaming : local_env -> Prename.t

val apply_pre : Prename.t -> local_env -> constr precondition ->
  constr precondition
val apply_post : Prename.t -> local_env -> string -> constr postcondition ->
  constr postcondition
val apply_assert : Prename.t -> local_env -> constr assertion ->
  constr assertion

val type_v_subst : (identifier * identifier) list -> type_v -> type_v
val type_c_subst : (identifier * identifier) list -> type_c -> type_c

val type_v_rsubst : (identifier * constr) list -> type_v -> type_v
val type_c_rsubst : (identifier * constr) list -> type_c -> type_c

val make_arrow : ('a ml_type_v binder) list -> 'a ml_type_c -> 'a ml_type_v

val is_mutable_in_env : local_env -> identifier -> bool
val now_vars : local_env -> constr -> identifier list

val deref_type : 'a ml_type_v -> 'a ml_type_v
val dearray_type : 'a ml_type_v -> 'a * 'a ml_type_v
val constant_unit : unit -> constr ml_type_v
val v_of_constr : constr -> constr ml_type_v
val c_of_constr : constr -> constr ml_type_c
val is_pure_cci : constr -> bool

(* pretty printers *)

val pp_type_v : type_v -> std_ppcmds
val pp_type_c : type_c -> std_ppcmds
val pp_cc_term : cc_term -> std_ppcmds

