(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Tac2dyn
open Tac2val

(** {5 Ltac2 FFI} *)

type 'a repr

val repr_of : 'a repr -> 'a -> valexpr
val repr_to : 'a repr -> valexpr -> 'a

val make_repr : ('a -> valexpr) -> (valexpr -> 'a) -> 'a repr

val map_repr : ('a -> 'b) -> ('b -> 'a) -> 'a repr -> 'b repr

(** These functions allow to convert back and forth between OCaml and Ltac2
    data representation. The [to_*] functions raise an anomaly whenever the data
    has not expected shape. *)

val of_unit : unit -> valexpr
val to_unit : valexpr -> unit
val unit : unit repr

val of_int : int -> valexpr
val to_int : valexpr -> int
val int : int repr

val of_bool : bool -> valexpr
val to_bool : valexpr -> bool
val bool : bool repr

val of_char : char -> valexpr
val to_char : valexpr -> char
val char : char repr

val of_bytes : Bytes.t -> valexpr
val to_bytes : valexpr -> Bytes.t
val bytes : Bytes.t repr

(** WARNING these functions copy *)
val of_string : string -> valexpr
val to_string : valexpr -> string
val string : string repr

val of_list : ('a -> valexpr) -> 'a list -> valexpr
val to_list : (valexpr -> 'a) -> valexpr -> 'a list
val list : 'a repr -> 'a list repr

val of_constr : EConstr.t -> valexpr
val to_constr : valexpr -> EConstr.t
val constr : EConstr.t repr

val of_matching_context : Constr_matching.context -> valexpr
val to_matching_context : valexpr -> Constr_matching.context
val matching_context : Constr_matching.context repr

val of_preterm : Ltac_pretype.closed_glob_constr -> valexpr
val to_preterm : valexpr -> Ltac_pretype.closed_glob_constr
val preterm : Ltac_pretype.closed_glob_constr repr

val of_cast : Constr.cast_kind -> valexpr
val to_cast : valexpr -> Constr.cast_kind
val cast : Constr.cast_kind repr

(** Toplevel representation of OCaml exceptions. Invariant: no [LtacError]
    should be used with [err]. *)
val of_err : Exninfo.iexn -> valexpr
val to_err : valexpr -> Exninfo.iexn
val err : Exninfo.iexn repr

val of_exn : Exninfo.iexn -> valexpr
val to_exn : valexpr -> Exninfo.iexn
val exn : Exninfo.iexn repr

val of_exninfo : Exninfo.info -> valexpr
val to_exninfo : valexpr -> Exninfo.info
val exninfo : Exninfo.info repr

val of_ident : Id.t -> valexpr
val to_ident : valexpr -> Id.t
val ident : Id.t repr

val of_closure : closure -> valexpr
val to_closure : valexpr -> closure
val closure : closure repr

val of_block : (int * valexpr array) -> valexpr
val to_block : valexpr -> (int * valexpr array)
val block : (int * valexpr array) repr

val of_array : ('a -> valexpr) -> 'a array -> valexpr
val to_array : (valexpr -> 'a) -> valexpr -> 'a array
val array : 'a repr -> 'a array repr

val of_tuple : valexpr array -> valexpr
val to_tuple : valexpr -> valexpr array

val of_pair : ('a -> valexpr) -> ('b -> valexpr) -> 'a * 'b -> valexpr
val to_pair : (valexpr -> 'a) -> (valexpr -> 'b) -> valexpr -> 'a * 'b
val pair : 'a repr -> 'b repr -> ('a * 'b) repr

val of_triple : ('a -> valexpr) -> ('b -> valexpr) -> ('c -> valexpr) -> 'a * 'b * 'c -> valexpr
val to_triple : (valexpr -> 'a) -> (valexpr -> 'b) -> (valexpr -> 'c) -> valexpr -> 'a * 'b * 'c
val triple : 'a repr -> 'b repr -> 'c repr -> ('a * 'b * 'c) repr

val of_option : ('a -> valexpr) -> 'a option -> valexpr
val to_option : (valexpr -> 'a) -> valexpr -> 'a option
val option : 'a repr -> 'a option repr

val of_pattern : Pattern.constr_pattern -> valexpr
val to_pattern : valexpr -> Pattern.constr_pattern
val pattern : Pattern.constr_pattern repr

val of_evar : Evar.t -> valexpr
val to_evar : valexpr -> Evar.t
val evar : Evar.t repr

val of_sort : ESorts.t -> valexpr
val to_sort : valexpr -> ESorts.t
val sort : ESorts.t repr

val of_pp : Pp.t -> valexpr
val to_pp : valexpr -> Pp.t
val pp : Pp.t repr

val of_transparent_state : TransparentState.t -> valexpr
val to_transparent_state : valexpr -> TransparentState.t
val transparent_state : TransparentState.t repr

val of_pretype_flags : Pretyping.inference_flags -> valexpr
val to_pretype_flags : valexpr -> Pretyping.inference_flags
val pretype_flags : Pretyping.inference_flags repr

val of_expected_type : Pretyping.typing_constraint -> valexpr
val to_expected_type : valexpr -> Pretyping.typing_constraint
val expected_type : Pretyping.typing_constraint repr

type ind_data = (Names.Ind.t * Declarations.mutual_inductive_body)

val of_ind_data : ind_data -> valexpr
val to_ind_data : valexpr -> ind_data
val ind_data : ind_data repr

val of_inductive : inductive -> valexpr
val to_inductive : valexpr -> inductive
val inductive : inductive repr

val of_constant : Constant.t -> valexpr
val to_constant : valexpr -> Constant.t
val constant : Constant.t repr

val of_constructor : constructor -> valexpr
val to_constructor : valexpr -> constructor
val constructor : constructor repr

val of_projection : Projection.t -> valexpr
val to_projection : valexpr -> Projection.t
val projection : Projection.t repr

val of_qvar : Sorts.QVar.t -> valexpr
val to_qvar : valexpr -> Sorts.QVar.t
val qvar : Sorts.QVar.t repr

val of_case : Constr.case_info -> valexpr
val to_case : valexpr -> Constr.case_info
val case : Constr.case_info repr

type binder = (Name.t EConstr.binder_annot * types)

val of_binder : binder -> valexpr
val to_binder : valexpr -> binder
val binder : binder repr

val of_instance : EConstr.EInstance.t -> valexpr
val to_instance : valexpr -> EConstr.EInstance.t
val instance : EConstr.EInstance.t repr

val of_reference : GlobRef.t -> valexpr
val to_reference : valexpr -> GlobRef.t
val reference : GlobRef.t repr

val of_ext : 'a Val.tag -> 'a -> valexpr
val to_ext : 'a Val.tag -> valexpr -> 'a
val repr_ext : 'a Val.tag -> 'a repr

val of_open : KerName.t * valexpr array -> valexpr
val to_open : valexpr -> KerName.t * valexpr array
val open_ : (KerName.t * valexpr array) repr

val of_free : Id.Set.t -> valexpr
val to_free : valexpr -> Id.Set.t
val free : Id.Set.t repr

val of_uint63 : Uint63.t -> valexpr
val to_uint63 : valexpr -> Uint63.t
val uint63 : Uint63.t repr

val of_float : Float64.t -> valexpr
val to_float : valexpr -> Float64.t
val float : Float64.t repr

val of_pstring : Pstring.t -> valexpr
val to_pstring : valexpr -> Pstring.t
val pstring : Pstring.t repr

type ('a, 'b) fun1

val app_fun1 : ('a, 'b) fun1 -> 'a repr -> 'b repr -> 'a -> 'b Proofview.tactic

val to_fun1 : 'a repr -> 'b repr -> valexpr -> ('a, 'b) fun1
val fun1 : 'a repr -> 'b repr -> ('a, 'b) fun1 repr

val valexpr : valexpr repr

(** Exception *)

exception LtacError of KerName.t * valexpr array
(** Ltac2-defined exceptions seen from OCaml side *)
