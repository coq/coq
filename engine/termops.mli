(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines various utilities for term manipulation that are not
    needed in the kernel. *)

open Names
open Constr
open Environ
open EConstr

(** about contexts *)
val push_rel_assum : Name.t EConstr.binder_annot * types -> env -> env
val push_rels_assum : (Name.t Constr.binder_annot * Constr.types) list -> env -> env

val lookup_rel_id : Id.t -> ('c, 't, 'r) Context.Rel.pt -> int * 'c option * 't
(** Associates the contents of an identifier in a [rel_context]. Raise
    [Not_found] if there is no such identifier. *)

(** Functions that build argument lists matching a block of binders or a context.
    [rel_vect n m] builds [|Rel (n+m);...;Rel(n+1)|]
*)
val rel_vect : int -> int -> Constr.constr array
val rel_list : int -> int -> constr list

(** Prod/Lambda/LetIn destructors on constr *)

val it_mkNamedProd_wo_LetIn : Constr.types -> Constr.named_context -> Constr.types

(* Ad hoc version reinserting letin, assuming the body is defined in
   the context where the letins are expanded *)
val it_mkLambda_or_LetIn_from_no_LetIn : Constr.constr -> Constr.rel_context -> Constr.constr

(** {6 Generic iterators on constr} *)

val map_constr_with_binders_left_to_right :
  Environ.env -> Evd.evar_map ->
  (rel_declaration -> 'a -> 'a) ->
  ('a -> constr -> constr) ->
    'a -> constr -> constr
val map_constr_with_full_binders :
  Environ.env -> Evd.evar_map ->
  (rel_declaration -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr

val fold_constr_with_full_binders : Environ.env -> Evd.evar_map ->
  (rel_declaration -> 'a -> 'a) ->
  ('a -> 'b -> constr -> 'b) ->
  'a -> 'b -> constr -> 'b

(**********************************************************************)

val strip_head_cast : Evd.evar_map -> constr -> constr
val drop_extra_implicit_args : Evd.evar_map -> constr -> constr

(** occur checks *)

exception Occur
val occur_meta : Evd.evar_map -> constr -> bool
val occur_existential : Evd.evar_map -> constr -> bool
val occur_meta_or_existential : Evd.evar_map -> constr -> bool
val occur_metavariable : Evd.evar_map -> metavariable -> constr -> bool
val occur_evar : Evd.evar_map -> Evar.t -> constr -> bool
val occur_var : env -> Evd.evar_map -> Id.t -> constr -> bool
val occur_var_indirectly : env -> Evd.evar_map -> Id.t -> constr -> GlobRef.t option
val occur_var_in_decl : env -> Evd.evar_map -> Id.t -> named_declaration -> bool
val occur_vars : env -> Evd.evar_map -> Id.Set.t -> constr -> bool
val occur_vars_in_decl : env -> Evd.evar_map -> Id.Set.t -> named_declaration -> bool

(** As {!occur_var} but assume the identifier not to be a section variable *)
val local_occur_var : Evd.evar_map -> Id.t -> constr -> bool
val local_occur_var_in_decl : Evd.evar_map -> Id.t -> named_declaration -> bool

val free_rels : Evd.evar_map -> constr -> Int.Set.t

(** [dependent m t] tests whether [m] is a subterm of [t] *)
val dependent : Evd.evar_map -> constr -> constr -> bool
val dependent_no_evar : Evd.evar_map -> constr -> constr -> bool
val dependent_in_decl : Evd.evar_map -> constr -> named_declaration -> bool
val count_occurrences : Evd.evar_map -> constr -> constr -> int
val collect_metas : Evd.evar_map -> constr -> int list
val collect_vars : Evd.evar_map -> constr -> Id.Set.t (** for visible vars only *)

(* Substitution of metavariables *)
type meta_value_map = (metavariable * Constr.constr) list
val subst_meta : meta_value_map -> Constr.constr -> Constr.constr
val isMetaOf : Evd.evar_map -> metavariable -> constr -> bool

(** Type assignment for metavariables *)
type meta_type_map = (metavariable * Constr.types) list

(** [pop c] lifts by -1 the positive indexes in [c] *)
val pop : constr -> constr

(** {6 ... } *)
(** Substitution of an arbitrary large term. Uses equality modulo
   reduction of let *)

(** [replace_term_gen eq arity e c] replaces matching subterms according to
    [eq] by [e] in [c]. If [arity] is non-zero applications of larger length
    are handled atomically. *)
val replace_term_gen :
  Evd.evar_map -> (Evd.evar_map -> int -> constr -> bool) ->
    int -> constr -> constr -> constr

(** [subst_term d c] replaces [d] by [Rel 1] in [c] *)
val subst_term : Evd.evar_map -> constr -> constr -> constr

(** [replace_term d e c] replaces [d] by [e] in [c] *)
val replace_term : Evd.evar_map -> constr -> constr -> constr -> constr

(** Alternative term equalities *)
val base_sort_cmp : Conversion.conv_pb -> Sorts.t -> Sorts.t -> bool
val compare_constr_univ : Environ.env -> Evd.evar_map -> (Conversion.conv_pb -> constr -> constr -> bool) ->
  Conversion.conv_pb -> constr -> constr -> bool
val constr_cmp : Environ.env -> Evd.evar_map -> Conversion.conv_pb -> constr -> constr -> bool
val eq_constr : Environ.env -> Evd.evar_map -> constr -> constr -> bool (* FIXME rename: erases universes*)

val eta_reduce_head : Evd.evar_map -> constr -> constr

(* Eta expand the instantiation of a context *)
val eta_expand_instantiation : ?evars:CClosure.evar_handler -> env ->
  Constr.constr array -> Constr.rel_context -> Constr.constr array

(** [prod_applist] [forall (x1:B1;...;xn:Bn), B] [a1...an] @return [B[a1...an]] *)
val prod_applist : Evd.evar_map -> constr -> constr list -> constr

(** In [prod_applist_decls n c args], [c] is supposed to have the
    form [∀Γ.c] with [Γ] of length [m] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded.
    Note that [n] counts both let-ins and prods, while the length of [args]
    only counts prods. In other words, varying [n] changes how many
    trailing let-ins are expanded. *)
val prod_applist_decls : Evd.evar_map -> int -> constr -> constr list -> constr

(** Remove recursively the casts around a term i.e.
   [strip_outer_cast (Cast (Cast ... (Cast c, t) ... ))] is [c]. *)
val strip_outer_cast : Evd.evar_map -> constr -> constr

(** [nb_lam sigma t] counts the number of head lambda abstractions in [t], ignoring casts.
    For instance on [fun x1 x2 x3 => c] (where [c] is not itself a lambda abstraction) it returns 3. *)
val nb_lam : Evd.evar_map -> constr -> int

(** [nb_prod sigma t] counts the number of head products in [t], ignoring casts. *)
val nb_prod : Evd.evar_map -> constr -> int

(** Variant of [nb_prod] which also does zeta-reduction (i.e. reduces let-ins) along the way. *)
val nb_prod_modulo_zeta : Evd.evar_map -> constr -> int

(** [last_arg sigma t] returns the last argument of [t].
    Fails if [t] is not an application. *)
val last_arg : Evd.evar_map -> constr -> constr

val adjust_app_list_size : constr -> constr list -> constr -> constr list ->
  (constr * constr list * constr * constr list)
val adjust_app_array_size : constr -> constr array -> constr -> constr array ->
  (constr * constr array * constr * constr array)

(** name contexts *)
type names_context = Name.t list
val add_name : Name.t -> names_context -> names_context
val lookup_name_of_rel : int -> names_context -> Name.t
val lookup_rel_of_name : Id.t -> names_context -> int
val empty_names_context : names_context
val ids_of_rel_context : ('c, 't, 'r) Context.Rel.pt -> Id.t list
val ids_of_named_context : ('c, 't, 'r) Context.Named.pt -> Id.t list
val ids_of_context : env -> Id.t list
val names_of_rel_context : env -> names_context

(* [env_rel_context_chop n env] extracts out the [n] top declarations
   of the rel_context part of [env], counting both local definitions and
   hypotheses *)
val env_rel_context_chop : int -> env -> env * rel_context

(** Set of local names *)
val vars_of_env: env -> Id.Set.t
val add_vname : Id.Set.t -> Name.t -> Id.Set.t

(** other signature iterators *)
val process_rel_context : (rel_declaration -> env -> env) -> env -> env
val assums_of_rel_context : ('c, 't, 'r) Context.Rel.pt -> ((Name.t,'r) Context.pbinder_annot * 't) list

val map_rel_context_in_env :
  (env -> Constr.constr -> Constr.constr) -> env -> Constr.rel_context -> Constr.rel_context
val fold_named_context_both_sides :
  ('a -> Constr.named_declaration -> Constr.named_declaration list -> 'a) ->
    Constr.named_context -> init:'a -> 'a
val mem_named_context_val : Id.t -> named_context_val -> bool

val clear_named_body : Id.t -> env -> env

val global_vars_set : env -> Evd.evar_map -> constr -> Id.Set.t
val global_vars_set_of_decl : env -> Evd.evar_map -> named_declaration -> Id.Set.t
val global_app_of_constr : env -> Evd.evar_map -> constr -> (GlobRef.t * EInstance.t) * constr option

(** Gives an ordered list of hypotheses, closed by dependencies,
   containing a given set *)
val dependency_closure : env -> Evd.evar_map -> named_context -> Id.Set.t -> Id.t list

(** This tests if the ident is known in the given env, intended to be used with the global env. *)
val is_section_variable : env -> Id.t -> bool
[@@deprecated "Use is_section_variable_env on the local env instead of is_section_variable on the global env."]

(** Check if the ident has [SecVar] status in this enviroment.
    By default [check=true] and produce anomaly if it is not bound.
    If [check=false] returns [false] if it is not bound. *)
val is_section_variable_sign : ?check:bool -> Environ.named_context_val -> Id.t -> bool
val is_section_variable_env : ?check:bool -> env -> Id.t -> bool

val is_template_polymorphic_ref : env -> Evd.evar_map -> constr -> bool
val is_template_polymorphic_ind : env -> Evd.evar_map -> constr -> bool

val is_Prop : Evd.evar_map -> constr -> bool
val is_Set : Evd.evar_map -> constr -> bool
val is_Type : Evd.evar_map -> constr -> bool

val reference_of_level : Evd.evar_map -> Univ.Level.t -> Libnames.qualid option

(** {5 Debug pretty-printers} *)

open Evd

val pr_global_env : env -> GlobRef.t -> Pp.t

val pr_existential_key : env -> evar_map -> Evar.t -> Pp.t
val evar_string : env -> evar_map -> Evar.t -> string

val evar_suggested_name : env -> evar_map -> Evar.t -> Id.t

val pr_evar_info : env -> evar_map -> 'a evar_info -> Pp.t
val pr_evar_constraints : evar_map -> evar_constraint list -> Pp.t
val pr_evar_map : ?with_univs:bool -> int option -> env -> evar_map -> Pp.t
val pr_evar_map_filter : ?with_univs:bool -> (Evar.t -> any_evar_info -> bool) ->
  env -> evar_map -> Pp.t
val pr_evd_level : evar_map -> Univ.Level.t -> Pp.t
val pr_evd_qglobal : evar_map -> Sorts.QGlobal.t -> Pp.t
val pr_evd_qvar : evar_map -> Sorts.QVar.t -> Pp.t
val pr_evd_quality : evar_map -> Sorts.Quality.t -> Pp.t
val pr_evd_universe : evar_map -> Univ.Universe.t -> Pp.t

(* Treat terms as a concrete data type with an otherwise unspecified
   representation. You should be wary about the lack of invariants of this API. *)
module ConstrData :
sig
type t = Constr.t
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
end

module Internal : sig

(** NOTE: to print terms you always want to use functions in
   Printer, not these ones which are for very special cases. *)

(** debug printers: print raw form for terms with evar-substitution.  *)
val debug_print_constr : evar_map -> constr -> Pp.t

(** Pretty-printer hook: [print_constr_env env sigma c] will pretty
   print c if the pretty printing layer has been linked into the Rocq
   binary. *)
val print_constr_env : env -> Evd.evar_map -> constr -> Pp.t

(** [set_print_constr f] sets f to be the pretty printer *)
val set_print_constr : (env -> Evd.evar_map -> constr -> Pp.t) -> unit

(** Printers for contexts *)
val print_named_context : env -> Evd.evar_map -> Pp.t
val pr_rel_decl : env -> Evd.evar_map -> Constr.rel_declaration -> Pp.t
val print_rel_context : env -> Evd.evar_map -> Pp.t
val print_env : env -> Evd.evar_map -> Pp.t

val print_kconstr : Environ.env -> Evd.evar_map -> Evd.econstr -> Pp.t

end

val pr_evar_universe_context : UState.t -> Pp.t
[@@deprecated "(9.0) Use [UState.pr] instead"]
