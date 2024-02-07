(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2expr

(** Names of ltac2 objects the plugin expects to exist. *)

(* Maybe we should use some sort of Register-like indirection layer to provide this stuff? *)

module Types : sig
  val unit : type_constant
  val list : type_constant
  val int : type_constant
  val string : type_constant
  val char : type_constant
  val ident : type_constant
  val uint63 : type_constant
  val float : type_constant
  val meta : type_constant
  val evar : type_constant
  val sort : type_constant
  val cast : type_constant
  val instance : type_constant
  val constant : type_constant
  val inductive : type_constant
  val constructor : type_constant
  val projection : type_constant
  val pattern : type_constant
  val constr : type_constant
  val preterm : type_constant
  val binder : type_constant
  val message : type_constant
  val format : type_constant
  val exn  : type_constant
  val array : type_constant
  val option : type_constant
  val bool : type_constant
  val result  : type_constant
  val err : type_constant
  val exninfo  : type_constant

  val reference : type_constant
  val occurrences : type_constant
  val intro_pattern : type_constant
  val bindings : type_constant
  val assertion : type_constant
  val clause : type_constant
  val induction_clause : type_constant
  val red_flags : type_constant
  val rewriting : type_constant
  val inversion_kind : type_constant
  val destruction_arg : type_constant
  val move_location : type_constant
  val hypothesis : type_constant
  val std_debug : type_constant
  val std_strategy : type_constant
  val orientation : type_constant

  val transparent_state : type_constant

  val constr_kind : type_constant
  val constr_case : type_constant

  val pretype_flags : type_constant
  val pretype_expected_type : type_constant

  val relevance : type_constant

  val matching_context : type_constant

  val match_kind : type_constant

  val free : type_constant

  val ind_data : type_constant

  val map_tag : type_constant

  val fset : type_constant
  val fmap : type_constant
end
