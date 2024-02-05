(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

val of_preterm : Ltac_pretype.closed_glob_constr -> valexpr
val to_preterm : valexpr -> Ltac_pretype.closed_glob_constr
val preterm : Ltac_pretype.closed_glob_constr repr

val of_cast : Constr.cast_kind -> valexpr
val to_cast : valexpr -> Constr.cast_kind
val cast : Constr.cast_kind repr

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

val of_pp : Pp.t -> valexpr
val to_pp : valexpr -> Pp.t
val pp : Pp.t repr

val of_constant : Constant.t -> valexpr
val to_constant : valexpr -> Constant.t
val constant : Constant.t repr

val of_reference : GlobRef.t -> valexpr
val to_reference : valexpr -> GlobRef.t
val reference : GlobRef.t repr

val of_ext : 'a Val.tag -> 'a -> valexpr
val to_ext : 'a Val.tag -> valexpr -> 'a
val repr_ext : 'a Val.tag -> 'a repr

val of_open : KerName.t * valexpr array -> valexpr
val to_open : valexpr -> KerName.t * valexpr array
val open_ : (KerName.t * valexpr array) repr

val of_uint63 : Uint63.t -> valexpr
val to_uint63 : valexpr -> Uint63.t
val uint63 : Uint63.t repr

val of_float : Float64.t -> valexpr
val to_float : valexpr -> Float64.t
val float : Float64.t repr

type ('a, 'b) fun1

val app_fun1 : ('a, 'b) fun1 -> 'a repr -> 'b repr -> 'a -> 'b Proofview.tactic

val to_fun1 : 'a repr -> 'b repr -> valexpr -> ('a, 'b) fun1
val fun1 : 'a repr -> 'b repr -> ('a, 'b) fun1 repr

val valexpr : valexpr repr

(** {5 Dynamic tags} *)

val val_constr : EConstr.t Val.tag
val val_ident : Id.t Val.tag
val val_pattern : Pattern.constr_pattern Val.tag
val val_preterm : Ltac_pretype.closed_glob_constr Val.tag
val val_matching_context : Constr_matching.context Val.tag
val val_evar : Evar.t Val.tag
val val_pp : Pp.t Val.tag
val val_sort : ESorts.t Val.tag
val val_cast : Constr.cast_kind Val.tag
val val_inductive : inductive Val.tag
val val_constant : Constant.t Val.tag
val val_constructor : constructor Val.tag
val val_projection : Projection.t Val.tag
val val_qvar : Sorts.QVar.t Val.tag
val val_case : Constr.case_info Val.tag
val val_binder : (Name.t Context.binder_annot * types) Val.tag
val val_univ : Univ.Level.t Val.tag
val val_quality : Sorts.Quality.t Val.tag
val val_free : Id.Set.t Val.tag
val val_uint63 : Uint63.t Val.tag
val val_float : Float64.t Val.tag
val val_ltac1 : Geninterp.Val.t Val.tag
val val_pretype_flags : Pretyping.inference_flags Val.tag
val val_expected_type : Pretyping.typing_constraint Val.tag

val val_ind_data : (Names.Ind.t * Declarations.mutual_inductive_body) Val.tag
val val_transparent_state : TransparentState.t Val.tag

val val_exninfo : Exninfo.info Tac2dyn.Val.tag
val val_exn : Exninfo.iexn Tac2dyn.Val.tag
(** Toplevel representation of OCaml exceptions. Invariant: no [LtacError]
    should be put into a value with tag [val_exn]. *)

(** Exception *)

exception LtacError of KerName.t * valexpr array
(** Ltac2-defined exceptions seen from OCaml side *)
