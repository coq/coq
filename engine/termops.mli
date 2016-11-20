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
val pr_fix : ('a -> std_ppcmds) -> ('a, 'a) pfixpoint -> std_ppcmds

(** debug printer: do not use to display terms to the casual user... *)
val set_print_constr : (env -> constr -> std_ppcmds) -> unit
val print_constr     : constr -> std_ppcmds
val print_constr_env : env -> constr -> std_ppcmds
val print_named_context : env -> std_ppcmds
val pr_rel_decl : env -> Context.Rel.Declaration.t -> std_ppcmds
val print_rel_context : env -> std_ppcmds
val print_env : env -> std_ppcmds

(** about contexts *)
val push_rel_assum : Name.t * EConstr.types -> env -> env
val push_rels_assum : (Name.t * types) list -> env -> env
val push_named_rec_types : Name.t array * types array * 'a -> env -> env

val lookup_rel_id : Id.t -> Context.Rel.t -> int * constr option * types
(** Associates the contents of an identifier in a [rel_context]. Raise
    [Not_found] if there is no such identifier. *)

(** Functions that build argument lists matching a block of binders or a context.
    [rel_vect n m] builds [|Rel (n+m);...;Rel(n+1)|]
*)
val rel_vect : int -> int -> constr array
val rel_list : int -> int -> EConstr.constr list

(** iterators/destructors on terms *)
val mkProd_or_LetIn : Context.Rel.Declaration.t -> types -> types
val mkProd_wo_LetIn : Context.Rel.Declaration.t -> EConstr.types -> EConstr.types
val it_mkProd : EConstr.types -> (Name.t * EConstr.types) list -> EConstr.types
val it_mkLambda : EConstr.constr -> (Name.t * EConstr.types) list -> EConstr.constr
val it_mkProd_or_LetIn : types -> Context.Rel.t -> types
val it_mkProd_wo_LetIn : EConstr.types -> Context.Rel.t -> EConstr.types
val it_mkLambda_or_LetIn : constr -> Context.Rel.t -> constr
val it_mkNamedProd_or_LetIn : EConstr.types -> Context.Named.t -> EConstr.types
val it_mkNamedProd_wo_LetIn : types -> Context.Named.t -> types
val it_mkNamedLambda_or_LetIn : EConstr.constr -> Context.Named.t -> EConstr.constr

(* Ad hoc version reinserting letin, assuming the body is defined in
   the context where the letins are expanded *)
val it_mkLambda_or_LetIn_from_no_LetIn : constr -> Context.Rel.t -> constr

(** {6 Generic iterators on constr} *)

val map_constr_with_named_binders :
  (Name.t -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr
val map_constr_with_binders_left_to_right :
  Evd.evar_map ->
  (Context.Rel.Declaration.t -> 'a -> 'a) ->
  ('a -> EConstr.constr -> EConstr.constr) ->
    'a -> EConstr.constr -> EConstr.constr
val map_constr_with_full_binders :
  Evd.evar_map ->
  (Context.Rel.Declaration.t -> 'a -> 'a) ->
  ('a -> EConstr.t -> EConstr.t) -> 'a -> EConstr.t -> EConstr.t

(** [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

val fold_constr_with_binders :
  Evd.evar_map -> ('a -> 'a) ->
    ('a -> 'b -> EConstr.t -> 'b) -> 'a -> 'b -> EConstr.t -> 'b

val fold_constr_with_full_binders :
  Evd.evar_map -> (Context.Rel.Declaration.t -> 'a -> 'a) ->
    ('a -> 'b -> EConstr.t -> 'b) -> 'a -> 'b -> EConstr.t -> 'b

val iter_constr_with_full_binders :
  (Context.Rel.Declaration.t -> 'a -> 'a) -> ('a -> constr -> unit) -> 'a ->
    constr -> unit

(**********************************************************************)

val strip_head_cast : Evd.evar_map -> EConstr.t -> EConstr.t
val drop_extra_implicit_args : Evd.evar_map -> EConstr.t -> EConstr.constr

(** occur checks *)

exception Occur
val occur_meta : Evd.evar_map -> EConstr.t -> bool
val occur_existential : Evd.evar_map -> EConstr.t -> bool
val occur_meta_or_existential : Evd.evar_map -> EConstr.t -> bool
val occur_evar : Evd.evar_map -> existential_key -> EConstr.t -> bool
val occur_var : env -> Evd.evar_map -> Id.t -> EConstr.t -> bool
val occur_var_in_decl :
  env -> Evd.evar_map ->
  Id.t -> Context.Named.Declaration.t -> bool

(** As {!occur_var} but assume the identifier not to be a section variable *)
val local_occur_var : Evd.evar_map -> Id.t -> EConstr.t -> bool

val free_rels : Evd.evar_map -> EConstr.t -> Int.Set.t

(** [dependent m t] tests whether [m] is a subterm of [t] *)
val dependent : Evd.evar_map -> EConstr.t -> EConstr.t -> bool
val dependent_no_evar : Evd.evar_map -> EConstr.t -> EConstr.t -> bool
val dependent_univs : Evd.evar_map -> EConstr.t -> EConstr.t -> bool
val dependent_univs_no_evar : Evd.evar_map -> EConstr.t -> EConstr.t -> bool
val dependent_in_decl : Evd.evar_map -> EConstr.t -> Context.Named.Declaration.t -> bool
val count_occurrences : Evd.evar_map -> EConstr.t -> EConstr.t -> int
val collect_metas : Evd.evar_map -> EConstr.t -> int list
val collect_vars : Evd.evar_map -> EConstr.t -> Id.Set.t (** for visible vars only *)
val vars_of_global_reference : env -> Globnames.global_reference -> Id.Set.t
val occur_term : Evd.evar_map -> EConstr.t -> EConstr.t -> bool (** Synonymous of dependent *)

(* Substitution of metavariables *)
type meta_value_map = (metavariable * constr) list
val subst_meta : meta_value_map -> constr -> constr

(** Type assignment for metavariables *)
type meta_type_map = (metavariable * types) list

(** [pop c] lifts by -1 the positive indexes in [c] *)
val pop : EConstr.t -> constr

(** {6 ... } *)
(** Substitution of an arbitrary large term. Uses equality modulo
   reduction of let *)

(** [subst_term_gen eq d c] replaces [d] by [Rel 1] in [c] using [eq]
   as equality *)
val subst_term_gen : Evd.evar_map ->
  (Evd.evar_map -> EConstr.t -> EConstr.t -> bool) -> EConstr.t -> EConstr.t -> constr

(** [replace_term_gen eq d e c] replaces [d] by [e] in [c] using [eq]
   as equality *)
val replace_term_gen :
  Evd.evar_map -> (Evd.evar_map -> EConstr.t -> EConstr.t -> bool) ->
    EConstr.t -> EConstr.t -> EConstr.t -> constr

(** [subst_term d c] replaces [d] by [Rel 1] in [c] *)
val subst_term : Evd.evar_map -> EConstr.t -> EConstr.t -> constr

(** [replace_term d e c] replaces [d] by [e] in [c] *)
val replace_term : Evd.evar_map -> EConstr.t -> EConstr.t -> EConstr.t -> constr

(** Alternative term equalities *)
val base_sort_cmp : Reduction.conv_pb -> sorts -> sorts -> bool
val compare_constr_univ : Evd.evar_map -> (Reduction.conv_pb -> EConstr.constr -> EConstr.constr -> bool) ->
  Reduction.conv_pb -> EConstr.constr -> EConstr.constr -> bool
val constr_cmp : Evd.evar_map -> Reduction.conv_pb -> EConstr.constr -> EConstr.constr -> bool
val eq_constr : Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool (* FIXME rename: erases universes*)

val eta_reduce_head : constr -> constr

(** Flattens application lists *)
val collapse_appl : Evd.evar_map -> EConstr.t -> constr

val prod_applist : Evd.evar_map -> EConstr.t -> EConstr.t list -> EConstr.t

(** Remove recursively the casts around a term i.e.
   [strip_outer_cast (Cast (Cast ... (Cast c, t) ... ))] is [c]. *)
val strip_outer_cast : Evd.evar_map -> EConstr.t -> constr

exception CannotFilter

(** Lightweight first-order filtering procedure. Unification
   variables ar represented by (untyped) Evars.
   [filtering c1 c2] returns the substitution n'th evar ->
   (context,term), or raises [CannotFilter].
   Warning: Outer-kernel sort subtyping are taken into account: c1 has
   to be smaller than c2 wrt. sorts. *)
type subst = (Context.Rel.t * constr) Evar.Map.t
val filtering : Evd.evar_map -> Context.Rel.t -> Reduction.conv_pb -> constr -> constr -> subst

val decompose_prod_letin : Evd.evar_map -> EConstr.t -> int * Context.Rel.t * constr
val align_prod_letin : Evd.evar_map -> EConstr.t -> EConstr.t -> Context.Rel.t * constr

(** [nb_lam] {% $ %}[x_1:T_1]...[x_n:T_n]c{% $ %} where {% $ %}c{% $ %} is not an abstraction
   gives {% $ %}n{% $ %} (casts are ignored) *)
val nb_lam : Evd.evar_map -> EConstr.t -> int

(** Similar to [nb_lam], but gives the number of products instead *)
val nb_prod : Evd.evar_map -> EConstr.t -> int

(** Similar to [nb_prod], but zeta-contracts let-in on the way *)
val nb_prod_modulo_zeta : Evd.evar_map -> EConstr.t -> int

(** Get the last arg of a constr intended to be an application *)
val last_arg : Evd.evar_map -> EConstr.t -> EConstr.constr

(** Force the decomposition of a term as an applicative one *)
val decompose_app_vect : Evd.evar_map -> EConstr.t -> constr * constr array

val adjust_app_list_size : constr -> constr list -> constr -> constr list ->
  (constr * constr list * constr * constr list)
val adjust_app_array_size : EConstr.constr -> EConstr.constr array -> EConstr.constr -> EConstr.constr array ->
  (EConstr.constr * EConstr.constr array * EConstr.constr * EConstr.constr array)

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
val compact_named_context : Context.Named.t -> Context.Compacted.t

val clear_named_body : Id.t -> env -> env

val global_vars : env -> Evd.evar_map -> EConstr.t -> Id.t list
val global_vars_set : env -> Evd.evar_map -> EConstr.t -> Id.Set.t
val global_vars_set_of_decl : env -> Evd.evar_map -> Context.Named.Declaration.t -> Id.Set.t
val global_app_of_constr : Evd.evar_map -> EConstr.constr -> Globnames.global_reference puniverses * EConstr.constr option

(** Gives an ordered list of hypotheses, closed by dependencies,
   containing a given set *)
val dependency_closure : env -> Evd.evar_map -> Context.Named.t -> Id.Set.t -> Id.t list

(** Test if an identifier is the basename of a global reference *)
val is_section_variable : Id.t -> bool

val global_of_constr : Evd.evar_map -> EConstr.constr -> Globnames.global_reference puniverses

val is_global : Evd.evar_map -> Globnames.global_reference -> EConstr.constr -> bool

val isGlobalRef : Evd.evar_map -> EConstr.t -> bool

val is_template_polymorphic : env -> Evd.evar_map -> EConstr.t -> bool

val is_Prop : Evd.evar_map -> EConstr.t -> bool

(** Combinators on judgments *)

val on_judgment       : ('a -> 'b) -> ('a, 'a) punsafe_judgment -> ('b, 'b) punsafe_judgment
val on_judgment_value : ('c -> 'c) -> ('c, 't) punsafe_judgment -> ('c, 't) punsafe_judgment
val on_judgment_type  : ('t -> 't) -> ('c, 't) punsafe_judgment -> ('c, 't) punsafe_judgment

(** {6 Functions to deal with impossible cases } *)
val set_impossible_default_clause : (unit -> (constr * types) Univ.in_universe_context_set) -> unit
val coq_unit_judge : unit -> EConstr.unsafe_judgment Univ.in_universe_context_set
