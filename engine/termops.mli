(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines various utilities for term manipulation that are not
    needed in the kernel. *)

open Names
open Constr
open Environ
open EConstr

(** printers *)
val print_sort : Sorts.t -> Pp.t
val pr_sort_family : Sorts.family -> Pp.t
val pr_fix : ('a -> Pp.t) -> ('a, 'a) pfixpoint -> Pp.t

(** about contexts *)
val push_rel_assum : Name.t * types -> env -> env
val push_rels_assum : (Name.t * Constr.types) list -> env -> env
val push_named_rec_types : Name.t array * Constr.types array * 'a -> env -> env

val lookup_rel_id : Id.t -> ('c, 't) Context.Rel.pt -> int * 'c option * 't
(** Associates the contents of an identifier in a [rel_context]. Raise
    [Not_found] if there is no such identifier. *)

(** Functions that build argument lists matching a block of binders or a context.
    [rel_vect n m] builds [|Rel (n+m);...;Rel(n+1)|]
*)
val rel_vect : int -> int -> Constr.constr array
val rel_list : int -> int -> constr list

(** iterators/destructors on terms *)
val mkProd_or_LetIn : rel_declaration -> types -> types
val mkProd_wo_LetIn : rel_declaration -> types -> types
val it_mkProd : types -> (Name.t * types) list -> types
val it_mkLambda : constr -> (Name.t * types) list -> constr
val it_mkProd_or_LetIn : types -> rel_context -> types
val it_mkProd_wo_LetIn : types -> rel_context -> types
val it_mkLambda_or_LetIn : Constr.constr -> Context.Rel.t -> Constr.constr
val it_mkNamedProd_or_LetIn : types -> named_context -> types
val it_mkNamedProd_wo_LetIn : Constr.types -> Context.Named.t -> Constr.types
val it_mkNamedLambda_or_LetIn : constr -> named_context -> constr

(* Ad hoc version reinserting letin, assuming the body is defined in
   the context where the letins are expanded *)
val it_mkLambda_or_LetIn_from_no_LetIn : Constr.constr -> Context.Rel.t -> Constr.constr

(** {6 Generic iterators on constr} *)

val map_constr_with_binders_left_to_right :
  Evd.evar_map ->
  (rel_declaration -> 'a -> 'a) ->
  ('a -> constr -> constr) ->
    'a -> constr -> constr
val map_constr_with_full_binders :
  Evd.evar_map ->
  (rel_declaration -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr

(** [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

val fold_constr_with_binders : Evd.evar_map ->
  ('a -> 'a) -> ('a -> 'b -> constr -> 'b) -> 'a -> 'b -> constr -> 'b

val fold_constr_with_full_binders : Evd.evar_map ->
  (Context.Rel.Declaration.t -> 'a -> 'a) -> ('a -> 'b -> constr -> 'b) ->
    'a -> 'b -> constr -> 'b

val iter_constr_with_full_binders :
  (Context.Rel.Declaration.t -> 'a -> 'a) -> ('a -> Constr.constr -> unit) -> 'a ->
    Constr.constr -> unit

(**********************************************************************)

val strip_head_cast : Evd.evar_map -> constr -> constr
val drop_extra_implicit_args : Evd.evar_map -> constr -> constr

(** occur checks *)

exception Occur
val occur_meta : Evd.evar_map -> constr -> bool
val occur_existential : Evd.evar_map -> constr -> bool
val occur_meta_or_existential : Evd.evar_map -> constr -> bool
val occur_evar : Evd.evar_map -> Evar.t -> constr -> bool
val occur_var : env -> Evd.evar_map -> Id.t -> constr -> bool
val occur_var_in_decl :
  env -> Evd.evar_map ->
  Id.t -> named_declaration -> bool

(** As {!occur_var} but assume the identifier not to be a section variable *)
val local_occur_var : Evd.evar_map -> Id.t -> constr -> bool

val free_rels : Evd.evar_map -> constr -> Int.Set.t

(** [dependent m t] tests whether [m] is a subterm of [t] *)
val dependent : Evd.evar_map -> constr -> constr -> bool
val dependent_no_evar : Evd.evar_map -> constr -> constr -> bool
val dependent_in_decl : Evd.evar_map -> constr -> named_declaration -> bool
val count_occurrences : Evd.evar_map -> constr -> constr -> int
val collect_metas : Evd.evar_map -> constr -> int list
val collect_vars : Evd.evar_map -> constr -> Id.Set.t (** for visible vars only *)
val vars_of_global_reference : env -> Globnames.global_reference -> Id.Set.t
val occur_term : Evd.evar_map -> constr -> constr -> bool (** Synonymous of dependent *)
[@@ocaml.deprecated "alias of Termops.dependent"]

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

(** [subst_term_gen eq d c] replaces [d] by [Rel 1] in [c] using [eq]
   as equality *)
val subst_term_gen : Evd.evar_map ->
  (Evd.evar_map -> constr -> constr -> bool) -> constr -> constr -> constr

(** [replace_term_gen eq d e c] replaces [d] by [e] in [c] using [eq]
   as equality *)
val replace_term_gen :
  Evd.evar_map -> (Evd.evar_map -> constr -> constr -> bool) ->
    constr -> constr -> constr -> constr

(** [subst_term d c] replaces [d] by [Rel 1] in [c] *)
val subst_term : Evd.evar_map -> constr -> constr -> constr

(** [replace_term d e c] replaces [d] by [e] in [c] *)
val replace_term : Evd.evar_map -> constr -> constr -> constr -> constr

(** Alternative term equalities *)
val base_sort_cmp : Reduction.conv_pb -> Sorts.t -> Sorts.t -> bool
val compare_constr_univ : Evd.evar_map -> (Reduction.conv_pb -> constr -> constr -> bool) ->
  Reduction.conv_pb -> constr -> constr -> bool
val constr_cmp : Evd.evar_map -> Reduction.conv_pb -> constr -> constr -> bool
val eq_constr : Evd.evar_map -> constr -> constr -> bool (* FIXME rename: erases universes*)

val eta_reduce_head : Evd.evar_map -> constr -> constr

(** Flattens application lists *)
val collapse_appl : Evd.evar_map -> constr -> constr

(** [prod_applist] [forall (x1:B1;...;xn:Bn), B] [a1...an] @return [B[a1...an]] *)
val prod_applist : Evd.evar_map -> constr -> constr list -> constr

(** In [prod_applist_assum n c args], [c] is supposed to have the
    form [∀Γ.c] with [Γ] of length [m] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded.
    Note that [n] counts both let-ins and prods, while the length of [args]
    only counts prods. In other words, varying [n] changes how many
    trailing let-ins are expanded. *)
val prod_applist_assum : Evd.evar_map -> int -> constr -> constr list -> constr

(** Remove recursively the casts around a term i.e.
   [strip_outer_cast (Cast (Cast ... (Cast c, t) ... ))] is [c]. *)
val strip_outer_cast : Evd.evar_map -> constr -> constr

exception CannotFilter

(** Lightweight first-order filtering procedure. Unification
   variables ar represented by (untyped) Evars.
   [filtering c1 c2] returns the substitution n'th evar ->
   (context,term), or raises [CannotFilter].
   Warning: Outer-kernel sort subtyping are taken into account: c1 has
   to be smaller than c2 wrt. sorts. *)
type subst = (rel_context * constr) Evar.Map.t
val filtering : Evd.evar_map -> rel_context -> Reduction.conv_pb -> constr -> constr -> subst

val decompose_prod_letin : Evd.evar_map -> constr -> int * rel_context * constr
val align_prod_letin : Evd.evar_map -> constr -> constr -> rel_context * constr

(** [nb_lam] {% $ %}[x_1:T_1]...[x_n:T_n]c{% $ %} where {% $ %}c{% $ %} is not an abstraction
   gives {% $ %}n{% $ %} (casts are ignored) *)
val nb_lam : Evd.evar_map -> constr -> int

(** Similar to [nb_lam], but gives the number of products instead *)
val nb_prod : Evd.evar_map -> constr -> int

(** Similar to [nb_prod], but zeta-contracts let-in on the way *)
val nb_prod_modulo_zeta : Evd.evar_map -> constr -> int

(** Get the last arg of a constr intended to be an application *)
val last_arg : Evd.evar_map -> constr -> constr

(** Force the decomposition of a term as an applicative one *)
val decompose_app_vect : Evd.evar_map -> constr -> constr * constr array

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
val ids_of_rel_context : ('c, 't) Context.Rel.pt -> Id.t list
val ids_of_named_context : ('c, 't) Context.Named.pt -> Id.t list
val ids_of_context : env -> Id.t list
val names_of_rel_context : env -> names_context

(* [context_chop n Γ] returns (Γ₁,Γ₂) such that [Γ]=[Γ₂Γ₁], [Γ₁] has
   [n] hypotheses, excluding local definitions, and [Γ₁], if not empty,
   starts with an hypothesis (i.e. [Γ₁] has the form empty or [x:A;Γ₁'] *)
val context_chop : int -> Context.Rel.t -> Context.Rel.t * Context.Rel.t

(* [env_rel_context_chop n env] extracts out the [n] top declarations
   of the rel_context part of [env], counting both local definitions and
   hypotheses *)
val env_rel_context_chop : int -> env -> env * rel_context

(** Set of local names *)
val vars_of_env: env -> Id.Set.t
val add_vname : Id.Set.t -> Name.t -> Id.Set.t

(** other signature iterators *)
val process_rel_context : (rel_declaration -> env -> env) -> env -> env
val assums_of_rel_context : ('c, 't) Context.Rel.pt -> (Name.t * 't) list
val lift_rel_context : int -> Context.Rel.t -> Context.Rel.t
val substl_rel_context : Constr.constr list -> Context.Rel.t -> Context.Rel.t
val smash_rel_context : Context.Rel.t -> Context.Rel.t (** expand lets in context *)

val map_rel_context_in_env :
  (env -> Constr.constr -> Constr.constr) -> env -> Context.Rel.t -> Context.Rel.t
val map_rel_context_with_binders :
  (int -> 'c -> 'c) -> ('c, 'c) Context.Rel.pt -> ('c, 'c) Context.Rel.pt
val fold_named_context_both_sides :
  ('a -> Context.Named.Declaration.t -> Context.Named.Declaration.t list -> 'a) ->
    Context.Named.t -> init:'a -> 'a
val mem_named_context_val : Id.t -> named_context_val -> bool
val compact_named_context : Context.Named.t -> Context.Compacted.t

val map_rel_decl : ('a -> 'b) -> ('a, 'a) Context.Rel.Declaration.pt -> ('b, 'b) Context.Rel.Declaration.pt
val map_named_decl : ('a -> 'b) -> ('a, 'a) Context.Named.Declaration.pt -> ('b, 'b) Context.Named.Declaration.pt

val clear_named_body : Id.t -> env -> env

val global_vars : env -> Evd.evar_map -> constr -> Id.t list
val global_vars_set : env -> Evd.evar_map -> constr -> Id.Set.t
val global_vars_set_of_decl : env -> Evd.evar_map -> named_declaration -> Id.Set.t
val global_app_of_constr : Evd.evar_map -> constr -> (Globnames.global_reference * EInstance.t) * constr option

(** Gives an ordered list of hypotheses, closed by dependencies,
   containing a given set *)
val dependency_closure : env -> Evd.evar_map -> named_context -> Id.Set.t -> Id.t list

(** Test if an identifier is the basename of a global reference *)
val is_section_variable : Id.t -> bool

val global_of_constr : Evd.evar_map -> constr -> Globnames.global_reference * EInstance.t

val is_global : Evd.evar_map -> Globnames.global_reference -> constr -> bool

val isGlobalRef : Evd.evar_map -> constr -> bool

val is_template_polymorphic : env -> Evd.evar_map -> constr -> bool

val is_Prop : Evd.evar_map -> constr -> bool
val is_Set : Evd.evar_map -> constr -> bool
val is_Type : Evd.evar_map -> constr -> bool

val reference_of_level : Evd.evar_map -> Univ.Level.t -> Libnames.reference

(** Combinators on judgments *)

val on_judgment       : ('a -> 'b) -> ('a, 'a) punsafe_judgment -> ('b, 'b) punsafe_judgment
val on_judgment_value : ('c -> 'c) -> ('c, 't) punsafe_judgment -> ('c, 't) punsafe_judgment
val on_judgment_type  : ('t -> 't) -> ('c, 't) punsafe_judgment -> ('c, 't) punsafe_judgment

(** {5 Debug pretty-printers} *)

open Evd

val pr_existential_key : evar_map -> Evar.t -> Pp.t

val pr_evar_suggested_name : Evar.t -> evar_map -> Id.t

val pr_evar_info : evar_info -> Pp.t
val pr_evar_constraints : evar_map -> evar_constraint list -> Pp.t
val pr_evar_map : ?with_univs:bool -> int option -> evar_map -> Pp.t
val pr_evar_map_filter : ?with_univs:bool -> (Evar.t -> evar_info -> bool) ->
  evar_map -> Pp.t
val pr_metaset : Metaset.t -> Pp.t
val pr_evar_universe_context : UState.t -> Pp.t
val pr_evd_level : evar_map -> Univ.Level.t -> Pp.t

(** debug printer: do not use to display terms to the casual user... *)

val set_print_constr : (env -> Evd.evar_map -> constr -> Pp.t) -> unit
val print_constr     : constr -> Pp.t
val print_constr_env : env -> Evd.evar_map -> constr -> Pp.t
val print_named_context : env -> Pp.t
val pr_rel_decl : env -> Context.Rel.Declaration.t -> Pp.t
val print_rel_context : env -> Pp.t
val print_env : env -> Pp.t
