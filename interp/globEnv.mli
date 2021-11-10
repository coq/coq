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
open Environ
open Evd
open EConstr
open Ltac_pretype
open Evarutil

(** Type of environment extended with naming and ltac interpretation data *)

type t

(** To embed constr in glob_constr *)

type 'a obj_interp_fun =
  ?loc:Loc.t -> poly:bool -> t -> Evd.evar_map -> Evardefine.type_constraint ->
  'a -> unsafe_judgment * Evd.evar_map

val register_constr_interp0 :
  ('r, 'g, 't) Genarg.genarg_type -> 'g obj_interp_fun -> unit

(** {6 Pretyping name management} *)

(** The following provides a level of abstraction for the kind of
    environment used for type inference (so-called pretyping); in
    particular:
    - it supports that term variables can be interpreted as Ltac
      variables pointing to the effective expected name
    - it incrementally and lazily computes the renaming of rel
      variables used to build purely-named evar contexts
*)

(** Build a pretyping environment from an ltac environment *)

val make : hypnaming:naming_mode -> env -> evar_map -> ltac_var_map -> t

(** Export the underlying environment *)

val env : t -> env
val renamed_env : t -> env
val lfun : t -> unbound_ltac_var_map

val vars_of_env : t -> Id.Set.t

(** Push to the environment, returning the declaration(s) with interpreted names *)

val push_rel : hypnaming:naming_mode -> evar_map -> rel_declaration -> t -> rel_declaration * t
val push_rel_context : hypnaming:naming_mode -> ?force_names:bool -> evar_map -> rel_context -> t -> rel_context * t
val push_rec_types : hypnaming:naming_mode -> evar_map -> Name.t Context.binder_annot array * constr array -> t -> Name.t Context.binder_annot array * t

(** Declare an evar using renaming information *)

val new_evar : t -> evar_map -> ?src:Evar_kinds.t Loc.located ->
  ?naming:Namegen.intro_pattern_naming_expr -> constr -> evar_map * constr

val new_type_evar : t -> evar_map -> src:Evar_kinds.t Loc.located -> evar_map * constr

(** [hide_variable env na id] tells to hide the binding of [id] in
    the ltac environment part of [env] and to additionally rebind
    it to [id'] in case [na] is some [Name id']. It is useful e.g.
    for the dual status of [y] as term and binder. This is the case
    of [match y return p with ... end] which implicitly denotes
    [match z as z return p with ... end] when [y] is bound to a
    variable [z] and [match t as y return p with ... end] when [y]
    is bound to a non-variable term [t]. In the latter case, the
    binding of [y] to [t] should be hidden in [p]. *)

val hide_variable : t -> Name.t -> Id.t -> t

(** In case a variable is not bound by a term binder, look if it has
    an interpretation as a term in the ltac_var_map *)

val interp_ltac_variable : ?loc:Loc.t -> (t -> Glob_term.glob_constr -> evar_map * unsafe_judgment) ->
  t -> evar_map -> Id.t -> evar_map * unsafe_judgment

(** Interp an identifier as an ltac variable bound to an identifier,
    or as the identifier itself if not bound to an ltac variable *)

val interp_ltac_id : t -> Id.t -> Id.t

(** Interpreting a generic argument, typically a "ltac:(...)", taking
    into account the possible renaming *)

val interp_glob_genarg : ?loc:Loc.t -> poly:bool -> t -> evar_map -> Evardefine.type_constraint ->
  Genarg.glob_generic_argument -> unsafe_judgment * evar_map
