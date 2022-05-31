(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Utility functions over ML types with meta. *)

val reset_meta_count : unit -> unit
val new_meta : 'a -> Miniml.ml_type

val type_subst_list : Miniml.ml_type list -> Miniml.ml_type -> Miniml.ml_type
val type_subst_vect : Miniml.ml_type array -> Miniml.ml_type -> Miniml.ml_type

val instantiation : Miniml.ml_schema -> Miniml.ml_type

val needs_magic : Miniml.ml_type * Miniml.ml_type -> bool
val put_magic_if : bool -> Miniml.ml_ast -> Miniml.ml_ast
val put_magic : Miniml.ml_type * Miniml.ml_type -> Miniml.ml_ast -> Miniml.ml_ast

val generalizable : Miniml.ml_ast -> bool

(*s ML type environment. *)

module Mlenv : sig
  type t
  val empty : t

  (* get the n-th more recently entered schema and instantiate it. *)
  val get : t -> int -> Miniml.ml_type

  (* Adding a type in an environment, after generalizing free meta *)
  val push_gen : t -> Miniml.ml_type -> t

  (* Adding a type with no [Tvar] *)
  val push_type : t -> Miniml.ml_type -> t

  (* Adding a type with no [Tvar] nor [Tmeta] *)
  val push_std_type : t -> Miniml.ml_type -> t
end

(*s Utility functions over ML types without meta *)

val type_mem_kn : Names.MutInd.t -> Miniml.ml_type -> bool

val type_maxvar : Miniml.ml_type -> int

val type_decomp : Miniml.ml_type -> Miniml.ml_type list * Miniml.ml_type
val type_recomp : Miniml.ml_type list * Miniml.ml_type -> Miniml.ml_type

val var2var' : Miniml.ml_type -> Miniml.ml_type

type abbrev_map = Names.GlobRef.t -> Miniml.ml_type option

val type_expand : abbrev_map -> Miniml.ml_type -> Miniml.ml_type
val type_simpl : Miniml.ml_type -> Miniml.ml_type
val type_to_sign : abbrev_map -> Miniml.ml_type -> Miniml.sign
val type_to_signature : abbrev_map -> Miniml.ml_type -> Miniml.signature
val type_expunge : abbrev_map -> Miniml.ml_type -> Miniml.ml_type
val type_expunge_from_sign : abbrev_map -> Miniml.signature -> Miniml.ml_type -> Miniml.ml_type

val eq_ml_type : Miniml.ml_type -> Miniml.ml_type -> bool
val isTdummy : Miniml.ml_type -> bool
val isMLdummy : Miniml.ml_ast -> bool
val isKill : Miniml.sign -> bool

val case_expunge : Miniml.signature -> Miniml.ml_ast -> Miniml.ml_ident list * Miniml.ml_ast
val term_expunge : Miniml.signature -> Miniml.ml_ident list * Miniml.ml_ast -> Miniml.ml_ast


(*s Special identifiers. [dummy_name] is to be used for dead code
    and will be printed as [_] in concrete (Caml) code. *)

val anonymous_name : Names.Id.t
val dummy_name : Names.Id.t
val id_of_name : Names.Name.t -> Names.Id.t
val id_of_mlid : Miniml.ml_ident -> Names.Id.t
val tmp_id : Miniml.ml_ident -> Miniml.ml_ident

(*s [collect_lambda MLlam(id1,...MLlam(idn,t)...)] returns
    the list [idn;...;id1] and the term [t]. *)

val collect_lams : Miniml.ml_ast -> Miniml.ml_ident list * Miniml.ml_ast
val collect_n_lams : int -> Miniml.ml_ast -> Miniml.ml_ident list * Miniml.ml_ast
val remove_n_lams : int -> Miniml.ml_ast -> Miniml.ml_ast
val nb_lams : Miniml.ml_ast -> int
val named_lams : Miniml.ml_ident list -> Miniml.ml_ast -> Miniml.ml_ast
val dummy_lams : Miniml.ml_ast -> int -> Miniml.ml_ast
val anonym_or_dummy_lams : Miniml.ml_ast -> Miniml.signature -> Miniml.ml_ast

val eta_args_sign : int -> Miniml.signature -> Miniml.ml_ast list

(*s Utility functions over ML terms. *)

val mlapp : Miniml.ml_ast -> Miniml.ml_ast list -> Miniml.ml_ast
val ast_map : (Miniml.ml_ast -> Miniml.ml_ast) -> Miniml.ml_ast -> Miniml.ml_ast
val ast_map_lift : (int -> Miniml.ml_ast -> Miniml.ml_ast) -> int -> Miniml.ml_ast -> Miniml.ml_ast
val ast_iter : (Miniml.ml_ast -> unit) -> Miniml.ml_ast -> unit
val ast_occurs : int -> Miniml.ml_ast -> bool
val ast_occurs_itvl : int -> int -> Miniml.ml_ast -> bool
val ast_lift : int -> Miniml.ml_ast -> Miniml.ml_ast
val ast_pop : Miniml.ml_ast -> Miniml.ml_ast
val ast_subst : Miniml.ml_ast -> Miniml.ml_ast -> Miniml.ml_ast

val ast_glob_subst : Miniml.ml_ast Table.Refmap'.t -> Miniml.ml_ast -> Miniml.ml_ast

val dump_unused_vars : Miniml.ml_ast -> Miniml.ml_ast

val normalize : Miniml.ml_ast -> Miniml.ml_ast
val optimize_fix : Miniml.ml_ast -> Miniml.ml_ast
val inline : Names.GlobRef.t -> Miniml.ml_ast -> bool

val is_basic_pattern : Miniml.ml_pattern -> bool
val has_deep_pattern : Miniml.ml_branch array -> bool
val is_regular_match : Miniml.ml_branch array -> bool

exception Impossible

(* Classification of signatures *)

type sign_kind =
  | EmptySig
  | NonLogicalSig (* at least a [Keep] *)
  | SafeLogicalSig (* only [Kill Ktype] *)
  | UnsafeLogicalSig (* No [Keep], not all [Kill Ktype] *)

val sign_kind : Miniml.signature -> sign_kind

val sign_no_final_keeps : Miniml.signature -> Miniml.signature
