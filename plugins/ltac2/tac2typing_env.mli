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
open Tac2expr

module TVar : sig
  type t

  val equal : t -> t -> bool

  module Map : CSig.MapS with type key = t
end

type t

(** default strict:true *)
val empty_env : ?strict:bool -> unit -> t

val set_rec : (KerName.t * int) Id.Map.t -> t -> t

val reject_unbound_tvar : t -> t

val env_strict : t -> bool

val env_name : t -> TVar.t -> string

val fresh_id : t -> TVar.t

val get_alias : lident -> t -> TVar.t

val find_rec_var : Id.t -> t -> (KerName.t * int) option

type mix_var =
| GVar of TVar.t
| LVar of int

type mix_type_scheme = int * mix_var glb_typexpr

val mem_var : Id.t -> t -> bool

val find_var : Id.t -> t -> mix_type_scheme

val is_used_var : Id.t -> t -> bool

val bound_vars : t -> Id.Set.t

val get_variable0 : (Id.t -> bool) -> tacref or_relid -> tacref Locus.or_var

val get_variable : t -> tacref or_relid -> tacref Locus.or_var

(** View function, allows to ensure head normal forms *)
val kind : t -> TVar.t glb_typexpr -> TVar.t glb_typexpr

val pr_glbtype : t -> TVar.t glb_typexpr -> Pp.t

val eq_or_tuple : ('a -> 'b -> bool) -> 'a or_tuple -> 'b or_tuple -> bool

exception CannotUnify of TVar.t glb_typexpr * TVar.t glb_typexpr

(** unify0 raises CannotUnify, unify raises usererror *)
val unify0 : t -> TVar.t glb_typexpr -> TVar.t glb_typexpr -> unit

val unify : ?loc:Loc.t -> t -> TVar.t glb_typexpr -> TVar.t glb_typexpr -> unit

val unify_arrow : ?loc:Loc.t -> t
  -> TVar.t glb_typexpr
  -> (Loc.t option * TVar.t glb_typexpr) list
  -> TVar.t glb_typexpr

val abstract_var : t -> TVar.t glb_typexpr -> mix_type_scheme

val monomorphic : TVar.t glb_typexpr -> mix_type_scheme

val polymorphic : type_scheme -> mix_type_scheme

val push_name : Name.t -> mix_type_scheme -> t -> t

val push_ids : mix_type_scheme Id.Map.t -> t -> t

val subst_type : ('a -> 'b glb_typexpr) -> 'a glb_typexpr -> 'b glb_typexpr

val normalize : t ->
  int ref * int glb_typexpr TVar.Map.t ref ->
  TVar.t glb_typexpr ->
  int glb_typexpr
