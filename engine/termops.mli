(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines various utilities for term manipulation that are not
    needed in the kernel. *)

open Pp
open Names
open Term
open Environ

(** printers *)
val print_sort : sorts -> std_ppcmds
val pr_sort_family : sorts_family -> std_ppcmds
val pr_fix : (constr -> std_ppcmds) -> fixpoint -> std_ppcmds

(** debug printer: do not use to display terms to the casual user... *)
val set_print_constr : (env -> constr -> std_ppcmds) -> unit
val print_constr     : constr -> std_ppcmds
val print_constr_env : env -> constr -> std_ppcmds
val print_named_context : env -> std_ppcmds
val pr_rel_decl : env -> Context.Rel.Declaration.t -> std_ppcmds
val print_rel_context : env -> std_ppcmds
val print_env : env -> std_ppcmds

(** about contexts *)
val push_rel_assum : Name.t * types -> env -> env
val push_rels_assum : (Name.t * types) list -> env -> env
val push_named_rec_types : Name.t array * types array * 'a -> env -> env

val lookup_rel_id : Id.t -> Context.Rel.t -> int * constr option * types
(** Associates the contents of an identifier in a [rel_context]. Raise
    [Not_found] if there is no such identifier. *)

(** Functions that build argument lists matching a block of binders or a context.
    [rel_vect n m] builds [|Rel (n+m);...;Rel(n+1)|]
*)
val rel_vect : int -> int -> constr array
val rel_list : int -> int -> constr list

(** iterators/destructors on terms *)
val mkProd_or_LetIn : Context.Rel.Declaration.t -> types -> types
val mkProd_wo_LetIn : Context.Rel.Declaration.t -> types -> types
val it_mkProd : types -> (Name.t * types) list -> types
val it_mkLambda : constr -> (Name.t * types) list -> constr
val it_mkProd_or_LetIn : types -> Context.Rel.t -> types
val it_mkProd_wo_LetIn : types -> Context.Rel.t -> types
val it_mkLambda_or_LetIn : constr -> Context.Rel.t -> constr
val it_mkNamedProd_or_LetIn : types -> Context.Named.t -> types
val it_mkNamedProd_wo_LetIn : types -> Context.Named.t -> types
val it_mkNamedLambda_or_LetIn : constr -> Context.Named.t -> constr

(* Ad hoc version reinserting letin, assuming the body is defined in
   the context where the letins are expanded *)
val it_mkLambda_or_LetIn_from_no_LetIn : constr -> Context.Rel.t -> constr

(** {6 Generic iterators on constr} *)

val map_constr_with_named_binders :
  (Name.t -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr
val map_constr_with_binders_left_to_right :
  (Context.Rel.Declaration.t -> 'a -> 'a) ->
  ('a -> constr -> constr) ->
    'a -> constr -> constr
val map_constr_with_full_binders :
  (Context.Rel.Declaration.t -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr

(** [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

val fold_constr_with_binders :
  ('a -> 'a) -> ('a -> 'b -> constr -> 'b) -> 'a -> 'b -> constr -> 'b

val fold_constr_with_full_binders :
  (Context.Rel.Declaration.t -> 'a -> 'a) -> ('a -> 'b -> constr -> 'b) ->
    'a -> 'b -> constr -> 'b

val iter_constr_with_full_binders :
  (Context.Rel.Declaration.t -> 'a -> 'a) -> ('a -> constr -> unit) -> 'a ->
    constr -> unit

(**********************************************************************)

val strip_head_cast : constr -> constr
val drop_extra_implicit_args : constr -> constr

(** occur checks *)

exception Occur
val occur_meta : types -> bool
val occur_existential : types -> bool
val occur_meta_or_existential : types -> bool
val occur_evar : existential_key -> types -> bool
val occur_var : env -> Id.t -> types -> bool
val occur_var_in_decl :
  env ->
  Id.t -> Context.Named.Declaration.t -> bool

(** As {!occur_var} but assume the identifier not to be a section variable *)
val local_occur_var : Id.t -> types -> bool

val free_rels : constr -> Int.Set.t

(** [dependent m t] tests whether [m] is a subterm of [t] *)
val dependent : constr -> constr -> bool
val dependent_no_evar : constr -> constr -> bool
val dependent_univs : constr -> constr -> bool
val dependent_univs_no_evar : constr -> constr -> bool
val dependent_in_decl : constr -> Context.Named.Declaration.t -> bool
val count_occurrences : constr -> constr -> int
val collect_metas : constr -> int list
val collect_vars : constr -> Id.Set.t (** for visible vars only *)
val occur_term : constr -> constr -> bool (** Synonymous
 of dependent 
   Substitution of metavariables *)
type meta_value_map = (metavariable * constr) list
val subst_meta : meta_value_map -> constr -> constr

(** Type assignment for metavariables *)
type meta_type_map = (metavariable * types) list

(** [pop c] lifts by -1 the positive indexes in [c] *)
val pop : constr -> constr

(** {6 ... } *)
(** Substitution of an arbitrary large term. Uses equality modulo
   reduction of let *)

(** [subst_term_gen eq d c] replaces [d] by [Rel 1] in [c] using [eq]
   as equality *)
val subst_term_gen :
  (constr -> constr -> bool) -> constr -> constr -> constr

(** [replace_term_gen eq d e c] replaces [d] by [e] in [c] using [eq]
   as equality *)
val replace_term_gen :
  (constr -> constr -> bool) ->
    constr -> constr -> constr -> constr

(** [subst_term d c] replaces [d] by [Rel 1] in [c] *)
val subst_term : constr -> constr -> constr

(** [replace_term d e c] replaces [d] by [e] in [c] *)
val replace_term : constr -> constr -> constr -> constr

(** Alternative term equalities *)
val base_sort_cmp : Reduction.conv_pb -> sorts -> sorts -> bool
val compare_constr_univ : (Reduction.conv_pb -> constr -> constr -> bool) ->
  Reduction.conv_pb -> constr -> constr -> bool
val constr_cmp : Reduction.conv_pb -> constr -> constr -> bool
val eq_constr : constr -> constr -> bool (* FIXME rename: erases universes*)

val eta_reduce_head : constr -> constr

exception CannotFilter

(** Lightweight first-order filtering procedure. Unification
   variables ar represented by (untyped) Evars.
   [filtering c1 c2] returns the substitution n'th evar ->
   (context,term), or raises [CannotFilter].
   Warning: Outer-kernel sort subtyping are taken into account: c1 has
   to be smaller than c2 wrt. sorts. *)
type subst = (Context.Rel.t * constr) Evar.Map.t
val filtering : Context.Rel.t -> Reduction.conv_pb -> constr -> constr -> subst

val decompose_prod_letin : constr -> int * Context.Rel.t * constr
val align_prod_letin : constr -> constr -> Context.Rel.t * constr

(** [nb_lam] {% $ %}[x_1:T_1]...[x_n:T_n]c{% $ %} where {% $ %}c{% $ %} is not an abstraction
   gives {% $ %}n{% $ %} (casts are ignored) *)
val nb_lam : constr -> int

(** Similar to [nb_lam], but gives the number of products instead *)
val nb_prod : constr -> int

(** Similar to [nb_prod], but zeta-contracts let-in on the way *)
val nb_prod_modulo_zeta : constr -> int

(** Get the last arg of a constr intended to be an application *)
val last_arg : constr -> constr

(** Force the decomposition of a term as an applicative one *)
val decompose_app_vect : constr -> constr * constr array

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
val ids_of_rel_context : Context.Rel.t -> Id.t list
val ids_of_named_context : Context.Named.t -> Id.t list
val ids_of_context : env -> Id.t list
val names_of_rel_context : env -> names_context

(* [context_chop n Γ] returns (Γ₁,Γ₂) such that [Γ]=[Γ₂Γ₁], [Γ₁] has
   [n] hypotheses, excluding local definitions, and [Γ₁], if not empty,
   starts with an hypothesis (i.e. [Γ₁] has the form empty or [x:A;Γ₁'] *)
val context_chop : int -> Context.Rel.t -> Context.Rel.t * Context.Rel.t

(* [env_rel_context_chop n env] extracts out the [n] top declarations
   of the rel_context part of [env], counting both local definitions and
   hypotheses *)
val env_rel_context_chop : int -> env -> env * Context.Rel.t

(** Set of local names *)
val vars_of_env: env -> Id.Set.t
val add_vname : Id.Set.t -> Name.t -> Id.Set.t

(** other signature iterators *)
val process_rel_context : (Context.Rel.Declaration.t -> env -> env) -> env -> env
val assums_of_rel_context : Context.Rel.t -> (Name.t * constr) list
val lift_rel_context : int -> Context.Rel.t -> Context.Rel.t
val substl_rel_context : constr list -> Context.Rel.t -> Context.Rel.t
val smash_rel_context : Context.Rel.t -> Context.Rel.t (** expand lets in context *)

val map_rel_context_in_env :
  (env -> constr -> constr) -> env -> Context.Rel.t -> Context.Rel.t
val map_rel_context_with_binders :
  (int -> constr -> constr) -> Context.Rel.t -> Context.Rel.t
val fold_named_context_both_sides :
  ('a -> Context.Named.Declaration.t -> Context.Named.Declaration.t list -> 'a) ->
    Context.Named.t -> init:'a -> 'a
val mem_named_context_val : Id.t -> named_context_val -> bool
val compact_named_context : Context.Named.t -> Context.NamedList.t
val compact_named_context_reverse : Context.Named.t -> Context.NamedList.t

val clear_named_body : Id.t -> env -> env

val global_vars : env -> constr -> Id.t list
val global_vars_set_of_decl : env -> Context.Named.Declaration.t -> Id.Set.t

(** Gives an ordered list of hypotheses, closed by dependencies,
   containing a given set *)
val dependency_closure : env -> Context.Named.t -> Id.Set.t -> Id.t list

(** Test if an identifier is the basename of a global reference *)
val is_section_variable : Id.t -> bool

val isGlobalRef : constr -> bool

val is_template_polymorphic : env -> constr -> bool

(** Combinators on judgments *)

val on_judgment       : (types -> types) -> unsafe_judgment -> unsafe_judgment
val on_judgment_value : (types -> types) -> unsafe_judgment -> unsafe_judgment
val on_judgment_type  : (types -> types) -> unsafe_judgment -> unsafe_judgment

(** {6 Functions to deal with impossible cases } *)
val set_impossible_default_clause : (unit -> (constr * types) Univ.in_universe_context_set) -> unit
val coq_unit_judge : unit -> unsafe_judgment Univ.in_universe_context_set
