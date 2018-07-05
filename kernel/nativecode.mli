(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names
open Constr
open Declarations
open Environ
open Nativelambda

(** This file defines the mllambda code generation phase of the native
compiler. mllambda represents a fragment of ML, and can easily be printed
to OCaml code. *)

type mllambda
type global

val pp_global : Format.formatter -> global -> unit

val mk_open : string -> global

(* Precomputed values for a compilation unit *)
type symbol
type symbols

val empty_symbols : symbols

val clear_symbols : unit -> unit

val get_value : symbols -> int -> Nativevalues.t

val get_sort : symbols -> int -> Sorts.t

val get_name : symbols -> int -> Name.t

val get_const : symbols -> int -> Constant.t

val get_match : symbols -> int -> Nativevalues.annot_sw

val get_ind : symbols -> int -> inductive

val get_meta : symbols -> int -> metavariable

val get_evar : symbols -> int -> Evar.t

val get_level : symbols -> int -> Univ.Level.t

val get_proj : symbols -> int -> inductive * int

val get_symbols : unit -> symbols

type code_location_update
type code_location_updates
type linkable_code = global list * code_location_updates

val clear_global_tbl : unit -> unit

val empty_updates : code_location_updates

val register_native_file : string -> unit

val compile_constant_field : env -> string -> Constant.t ->
  global list -> constant_body -> global list

val compile_mind_field : ModPath.t -> Label.t ->
  global list -> mutual_inductive_body -> global list

val mk_conv_code : env -> evars -> string -> constr -> constr -> linkable_code
val mk_norm_code : env -> evars -> string -> constr -> linkable_code

val mk_library_header : DirPath.t -> global list

val mod_uid_of_dirpath : DirPath.t -> string

val link_info_of_dirpath : DirPath.t -> link_info

val update_locations : code_location_updates -> unit

val add_header_comment : global list -> string -> global list
