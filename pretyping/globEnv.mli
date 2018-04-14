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
open Environ
open Evd
open EConstr
open Ltac_pretype

(** To embed constr in glob_constr *)

val register_constr_interp0 :
  ('r, 'g, 't) Genarg.genarg_type ->
    (unbound_ltac_var_map -> env -> evar_map -> types -> 'g -> constr * evar_map) -> unit

(** {6 Pretyping name management} *)

(** The following provides a level of abstraction for the kind of
    environment used for type inference (so-called pretyping); in
    particular:
    - it supports that term variables can be interpreted as Ltac
      variables pointing to the effective expected name
    - it incrementally and lazily computes the renaming of rel
      variables used to build purely-named evar contexts
*)

(** Type of environment extended with naming and ltac interpretation data *)

type t

(** Build a pretyping environment from an ltac environment *)

val make : env -> evar_map -> ltac_var_map -> t

(** Export the underlying environement *)

val env : t -> env

(** Push to the environment, returning the declaration(s) with interpreted names *)

val push_rel : evar_map -> rel_declaration -> t -> rel_declaration * t
val push_rel_context : ?force_names:bool -> evar_map -> rel_context -> t -> rel_context * t
val push_rec_types : evar_map -> Name.t array * constr array -> t -> Name.t array * t

(** Declare an evar using renaming information *)

val e_new_evar : t -> evar_map ref -> ?src:Evar_kinds.t Loc.located ->
  ?naming:Namegen.intro_pattern_naming_expr -> constr -> constr

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

val interp_ltac_variable : ?loc:Loc.t -> (t -> Glob_term.glob_constr -> unsafe_judgment) ->
  t -> evar_map -> Id.t -> unsafe_judgment

(** Interpreting a generic argument, typically a "ltac:(...)", taking
    into account the possible renaming *)

val interp_glob_genarg : t -> evar_map -> constr ->
  Genarg.glob_generic_argument -> constr * evar_map
