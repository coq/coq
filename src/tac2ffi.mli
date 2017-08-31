(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open EConstr
open Tac2dyn
open Tac2expr

(** {5 Ltac2 FFI} *)

(** These functions allow to convert back and forth between OCaml and Ltac2
    data representation. The [to_*] functions raise an anomaly whenever the data
    has not expected shape. *)

val of_unit : unit -> valexpr
val to_unit : valexpr -> unit

val of_int : int -> valexpr
val to_int : valexpr -> int

val of_bool : bool -> valexpr
val to_bool : valexpr -> bool

val of_char : char -> valexpr
val to_char : valexpr -> char

val of_string : string -> valexpr
val to_string : valexpr -> string

val of_list : ('a -> valexpr) -> 'a list -> valexpr
val to_list : (valexpr -> 'a) -> valexpr -> 'a list

val of_constr : EConstr.t -> valexpr
val to_constr : valexpr -> EConstr.t

val of_exn : Exninfo.iexn -> valexpr
val to_exn : valexpr -> Exninfo.iexn

val of_ident : Id.t -> valexpr
val to_ident : valexpr -> Id.t

val of_array : ('a -> valexpr) -> 'a array -> valexpr
val to_array : (valexpr -> 'a) -> valexpr -> 'a array

val of_tuple : valexpr array -> valexpr
val to_tuple : valexpr -> valexpr array

val of_option : ('a -> valexpr) -> 'a option -> valexpr
val to_option : (valexpr -> 'a) -> valexpr -> 'a option

val of_pattern : Pattern.constr_pattern -> valexpr
val to_pattern : valexpr -> Pattern.constr_pattern

val of_pp : Pp.t -> valexpr
val to_pp : valexpr -> Pp.t

val of_constant : Constant.t -> valexpr
val to_constant : valexpr -> Constant.t

val of_reference : Globnames.global_reference -> valexpr
val to_reference : valexpr -> Globnames.global_reference

val of_ext : 'a Val.tag -> 'a -> valexpr
val to_ext : 'a Val.tag -> valexpr -> 'a

(** {5 Dynamic tags} *)

val val_constr : EConstr.t Val.tag
val val_ident : Id.t Val.tag
val val_pattern : Pattern.constr_pattern Val.tag
val val_pp : Pp.t Val.tag
val val_sort : ESorts.t Val.tag
val val_cast : Constr.cast_kind Val.tag
val val_inductive : inductive Val.tag
val val_constant : Constant.t Val.tag
val val_constructor : constructor Val.tag
val val_projection : Projection.t Val.tag
val val_case : Constr.case_info Val.tag
val val_univ : Univ.universe_level Val.tag
val val_kont : (Exninfo.iexn -> valexpr Proofview.tactic) Val.tag
val val_free : Id.Set.t Val.tag

val val_exn : Exninfo.iexn Tac2dyn.Val.tag
(** Toplevel representation of OCaml exceptions. Invariant: no [LtacError]
    should be put into a value with tag [val_exn]. *)
