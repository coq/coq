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

(** Type annotations. *)

module Types : sig

  type t
  (** Type of an argument of an external. This is basically
      [int Tac2expr.glb_typexpr] but we may add some smart constructors
      so that the user doesn't need to pick a number for variables used only once. *)

  val any : t

  val default : t option -> t

  val var : int -> t

  val tuple : t list -> t

  val (!) : Tac2expr.type_constant -> t list -> t

  val (!!) : Tac2expr.type_constant -> t
  (** Alias of [(!)] for 0-ary type formers. *)

  val (@->) : t -> t -> t

  val as_scheme : t -> Tac2expr.type_scheme

end

type 'a annotated = 'a * Types.t option

val typed : 'r -> Types.t -> 'r annotated
val untyped : 'r -> 'r annotated

(** These functions allow to convert back and forth between OCaml and Ltac2
    data representation. The [to_*] functions raise an anomaly whenever the data
    has not expected shape.

    Unless no default annotation is useful, [foo_] is the raw converter
    and [foo] annotates it with types taking any necessary type arguments.
*)

val of_unit : unit -> valexpr
val to_unit : valexpr -> unit
val unit : unit repr annotated
val unit_ : unit repr

val of_int : int -> valexpr
val to_int : valexpr -> int
val int : int repr annotated
val int_ : int repr

val of_bool : bool -> valexpr
val to_bool : valexpr -> bool
val bool : bool repr annotated
val bool_ : bool repr

val of_char : char -> valexpr
val to_char : valexpr -> char
val char : char repr annotated
val char_ : char repr

val of_bytes : Bytes.t -> valexpr
val to_bytes : valexpr -> Bytes.t
val bytes : Bytes.t repr annotated
val bytes_ : Bytes.t repr

(** WARNING these functions copy *)
val of_string : string -> valexpr
val to_string : valexpr -> string
val string : string repr annotated
val string_ : string repr

val of_list : ('a -> valexpr) -> 'a list -> valexpr
val to_list : (valexpr -> 'a) -> valexpr -> 'a list
val list : 'a repr annotated -> 'a list repr annotated
val list_ : 'a repr -> 'a list repr

val of_constr : EConstr.t -> valexpr
val to_constr : valexpr -> EConstr.t
val constr : EConstr.t repr annotated
val constr_ : EConstr.t repr

val of_preterm : Ltac_pretype.closed_glob_constr -> valexpr
val to_preterm : valexpr -> Ltac_pretype.closed_glob_constr
val preterm : Ltac_pretype.closed_glob_constr repr annotated
val preterm_ : Ltac_pretype.closed_glob_constr repr

val of_cast : Constr.cast_kind -> valexpr
val to_cast : valexpr -> Constr.cast_kind
val cast : Constr.cast_kind repr annotated
val cast_ : Constr.cast_kind repr

val of_err : Exninfo.iexn -> valexpr
val to_err : valexpr -> Exninfo.iexn
val err : Exninfo.iexn repr annotated
val err_ : Exninfo.iexn repr

val of_exn : Exninfo.iexn -> valexpr
val to_exn : valexpr -> Exninfo.iexn
val exn : Exninfo.iexn repr annotated
val exn_ : Exninfo.iexn repr

val of_result : ('a -> valexpr) -> ('a, Exninfo.iexn) result -> valexpr
val to_result : (valexpr -> 'a) -> valexpr -> ('a, Exninfo.iexn) result
val result_ : 'a repr -> ('a, Exninfo.iexn) result repr
val result  : 'a repr annotated -> ('a, Exninfo.iexn) result repr annotated

val of_exninfo : Exninfo.info -> valexpr
val to_exninfo : valexpr -> Exninfo.info
val exninfo : Exninfo.info repr annotated
val exninfo_ : Exninfo.info repr

val of_ident : Id.t -> valexpr
val to_ident : valexpr -> Id.t
val ident : Id.t repr annotated
val ident_ : Id.t repr

val of_closure : closure -> valexpr
val to_closure : valexpr -> closure
val closure : closure repr

val of_block : (int * valexpr array) -> valexpr
val to_block : valexpr -> (int * valexpr array)
val block : (int * valexpr array) repr

val of_array : ('a -> valexpr) -> 'a array -> valexpr
val to_array : (valexpr -> 'a) -> valexpr -> 'a array
val array : 'a repr annotated -> 'a array repr annotated
val array_ : 'a repr -> 'a array repr

val of_tuple : valexpr array -> valexpr
val to_tuple : valexpr -> valexpr array

val of_pair : ('a -> valexpr) -> ('b -> valexpr) -> 'a * 'b -> valexpr
val to_pair : (valexpr -> 'a) -> (valexpr -> 'b) -> valexpr -> 'a * 'b
val pair : 'a repr annotated -> 'b repr annotated -> ('a * 'b) repr annotated
val pair_ : 'a repr -> 'b repr -> ('a * 'b) repr

val of_triple : ('a -> valexpr) -> ('b -> valexpr) -> ('c -> valexpr) -> 'a * 'b * 'c -> valexpr
val to_triple : (valexpr -> 'a) -> (valexpr -> 'b) -> (valexpr -> 'c) -> valexpr -> 'a * 'b * 'c
val triple : 'a repr annotated -> 'b repr annotated -> 'c repr annotated -> ('a * 'b * 'c) repr annotated
val triple_ : 'a repr -> 'b repr -> 'c repr -> ('a * 'b * 'c) repr

val of_option : ('a -> valexpr) -> 'a option -> valexpr
val to_option : (valexpr -> 'a) -> valexpr -> 'a option
val option : 'a repr annotated -> 'a option repr annotated
val option_ : 'a repr -> 'a option repr

val of_pattern : Pattern.constr_pattern -> valexpr
val to_pattern : valexpr -> Pattern.constr_pattern
val pattern : Pattern.constr_pattern repr annotated
val pattern_ : Pattern.constr_pattern repr

val of_evar : Evar.t -> valexpr
val to_evar : valexpr -> Evar.t
val evar : Evar.t repr annotated
val evar_ : Evar.t repr

val of_pp : Pp.t -> valexpr
val to_pp : valexpr -> Pp.t
val pp : Pp.t repr annotated
val pp_ : Pp.t repr

val of_constant : Constant.t -> valexpr
val to_constant : valexpr -> Constant.t
val constant : Constant.t repr annotated
val constant_ : Constant.t repr

val of_reference : GlobRef.t -> valexpr
val to_reference : valexpr -> GlobRef.t
val reference : GlobRef.t repr annotated
val reference_ : GlobRef.t repr

val of_ext : 'a Val.tag -> 'a -> valexpr
val to_ext : 'a Val.tag -> valexpr -> 'a
val repr_ext : 'a Val.tag -> 'a repr

val of_open : KerName.t * valexpr array -> valexpr
val to_open : valexpr -> KerName.t * valexpr array
val open_ : (KerName.t * valexpr array) repr

val of_uint63 : Uint63.t -> valexpr
val to_uint63 : valexpr -> Uint63.t
val uint63 : Uint63.t repr annotated
val uint63_ : Uint63.t repr

val of_float : Float64.t -> valexpr
val to_float : valexpr -> Float64.t
val float : Float64.t repr annotated
val float_ : Float64.t repr

val thaw : (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic
(** The OCaml closure is suppoed to be pure, with any effects being inside the [tactic] value. *)

val to_fun1 : ('a -> valexpr) -> (valexpr -> 'r) -> valexpr -> 'a -> 'r Proofview.tactic
val of_fun1 : (valexpr -> 'a) -> ('r -> valexpr) -> ('a -> 'r Proofview.tactic) -> valexpr
val fun1_ : 'a repr -> 'r repr -> ('a -> 'r Proofview.tactic) repr
val fun1 : 'a repr annotated -> 'r repr annotated -> ('a -> 'r Proofview.tactic) repr annotated

val thunk : 'a repr annotated -> (unit -> 'a Proofview.tactic) repr annotated

val to_fun2 : ('a -> valexpr) -> ('b -> valexpr) -> (valexpr -> 'r) -> valexpr -> 'a -> 'b -> 'r Proofview.tactic
val of_fun2 : (valexpr -> 'a) -> (valexpr -> 'b) -> ('r -> valexpr) -> ('a -> 'b -> 'r Proofview.tactic) -> valexpr
val fun2_ : 'a repr -> 'b repr -> 'r repr -> ('a -> 'b -> 'r Proofview.tactic) repr
val fun2 : 'a repr annotated -> 'b repr annotated -> 'r repr annotated -> ('a -> 'b -> 'r Proofview.tactic) repr annotated

val to_fun3 : ('a -> valexpr) -> ('b -> valexpr) -> ('c -> valexpr) -> (valexpr -> 'r) -> valexpr -> 'a -> 'b -> 'c -> 'r Proofview.tactic
val of_fun3 : (valexpr -> 'a) -> (valexpr -> 'b) -> (valexpr -> 'c) -> ('r -> valexpr) -> ('a -> 'b -> 'c -> 'r Proofview.tactic) -> valexpr
val fun3_ : 'a repr -> 'b repr -> 'c repr -> 'r repr -> ('a -> 'b -> 'c -> 'r Proofview.tactic) repr
val fun3 : 'a repr annotated -> 'b repr annotated -> 'c repr annotated -> 'r repr annotated -> ('a -> 'b -> 'c -> 'r Proofview.tactic) repr annotated

val valexpr : valexpr repr

(** Most common use of valexpr is at type var 0. *)
val valexpr_0 : valexpr repr annotated

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
