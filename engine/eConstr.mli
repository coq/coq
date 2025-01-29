(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CSig
open Names
open Constr
open Environ

type t = Evd.econstr
(** Type of incomplete terms. Essentially a wrapper around {!Constr.t} ensuring
    that {!Constr.kind} does not observe defined evars. *)

(** {5 Universe variables} *)

module ERelevance :
sig
  type t = Evd.erelevance
  (** Type of relevance marks up-to quality variable unification. *)

  val make : Sorts.relevance -> t

  val kind : Evd.evar_map -> t -> Sorts.relevance

  val equal : Evd.evar_map -> t -> t -> bool

  val relevant : t
  val irrelevant : t

  val is_irrelevant : Evd.evar_map -> t -> bool
end

module ESorts :
sig
  type t = Evd.esorts
  (** Type of sorts up-to universe unification. Essentially a wrapper around
      Sorts.t so that normalization is ensured statically. *)

  val make : Sorts.t -> t
  (** Turn a sort into an up-to sort. *)

  val kind : Evd.evar_map -> t -> Sorts.t
  (** Returns the view into the current sort. Note that the kind of a variable
      may change if the unification state of the evar map changes. *)

  val equal : Evd.evar_map -> t -> t -> bool

  val is_small : Evd.evar_map -> t -> bool
  val is_prop : Evd.evar_map -> t -> bool
  val is_sprop : Evd.evar_map -> t -> bool
  val is_set : Evd.evar_map -> t -> bool

  val prop : t
  val sprop : t
  val set : t
  val type1 : t

  val super : Evd.evar_map -> t -> t

  val relevance_of_sort : t -> ERelevance.t

  val family : Evd.evar_map -> t -> Sorts.family

  val quality : Evd.evar_map -> t -> Sorts.Quality.t

end

module EInstance :
sig
  type t
  (** Type of universe instances up-to universe unification. Similar to
      [ESorts.t] for [UVars.Instance.t]. *)

  val make : UVars.Instance.t -> t
  val kind : Evd.evar_map -> t -> UVars.Instance.t
  val empty : t
  val is_empty : t -> bool
  val length : t -> int * int
end

type types = t
type constr = t
type existential = t pexistential
type case_return = (t,ERelevance.t) pcase_return
type case_branch = (t,ERelevance.t) pcase_branch
type rec_declaration = (t, t, ERelevance.t) prec_declaration
type fixpoint = (t, t, ERelevance.t) pfixpoint
type cofixpoint = (t, t, ERelevance.t) pcofixpoint
type unsafe_judgment = (constr, types) Environ.punsafe_judgment
type unsafe_type_judgment = (types, Evd.esorts) Environ.punsafe_type_judgment
type named_declaration = (constr, types, ERelevance.t) Context.Named.Declaration.pt
type rel_declaration = (constr, types, ERelevance.t) Context.Rel.Declaration.pt
type compacted_declaration = (constr, types, ERelevance.t) Context.Compacted.Declaration.pt
type named_context = (constr, types, ERelevance.t) Context.Named.pt
type compacted_context = compacted_declaration list
type rel_context = (constr, types, ERelevance.t) Context.Rel.pt
type 'a binder_annot = ('a,ERelevance.t) Context.pbinder_annot

val annotR : 'a -> 'a binder_annot
val nameR : Id.t -> Name.t binder_annot
val anonR : Name.t binder_annot

type case_invert = t pcase_invert
type case = (t, t, EInstance.t, ERelevance.t) pcase

type 'a puniverses = 'a * EInstance.t

(** {5 Destructors} *)

val kind : Evd.evar_map -> t -> (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term
(** Same as {!Constr.kind} except that it expands evars and normalizes
    universes on the fly. *)

val kind_upto : Evd.evar_map -> Constr.t ->
  (Constr.t, Constr.t, Sorts.t, UVars.Instance.t, Sorts.relevance) Constr.kind_of_term

val to_constr : ?abort_on_undefined_evars:bool -> Evd.evar_map -> t -> Constr.t
(** Returns the evar-normal form of the argument. Note that this
   function is supposed to be called when the original term has not
   more free-evars anymore. If you need compatibility with the old
   semantics, set [abort_on_undefined_evars] to [false].

    For getting the evar-normal form of a term with evars see
   {!Evarutil.nf_evar}. *)

val to_constr_opt : Evd.evar_map -> t -> Constr.t option
(** Same as [to_constr], but returns [None] if some unresolved evars remain *)

type kind_of_type =
  | SortType   of ESorts.t
  | CastType   of types * t
  | ProdType   of Name.t binder_annot * t * t
  | LetInType  of Name.t binder_annot * t * t * t
  | AtomicType of t * t array

val kind_of_type : Evd.evar_map -> t -> kind_of_type

(** {5 Constructors} *)

val of_kind : (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term -> t
(** Construct a term from a view. *)

val of_constr : Constr.t -> t
(** Translate a kernel term into an incomplete term in O(1). *)

(** {5 Insensitive primitives}

  Evar-insensitive versions of the corresponding functions. See the {!Constr}
  module for more information.

*)

(** {6 Constructors} *)

val mkRel : int -> t
val mkVar : Id.t -> t
val mkMeta : metavariable -> t
val mkEvar : t pexistential -> t
val mkSort : ESorts.t -> t
val mkSProp : t
val mkProp : t
val mkSet  : t
val mkType : Univ.Universe.t -> t
val mkCast : t * cast_kind * t -> t
val mkProd : Name.t binder_annot * t * t -> t
val mkLambda : Name.t binder_annot * t * t -> t
val mkLetIn : Name.t binder_annot * t * t * t -> t
val mkApp : t * t array -> t
val mkConstU : Constant.t * EInstance.t -> t
val mkProj : (Projection.t * ERelevance.t * t) -> t
val mkIndU : inductive * EInstance.t -> t
val mkConstructU : constructor * EInstance.t -> t
val mkConstructUi : (inductive * EInstance.t) * int -> t
val mkCase : case -> t
val mkFix : (t, t, ERelevance.t) pfixpoint -> t
val mkCoFix : (t, t, ERelevance.t) pcofixpoint -> t
val mkArrow : t -> ERelevance.t  -> t -> t
val mkArrowR : t -> t -> t
val mkInt : Uint63.t -> t
val mkFloat : Float64.t -> t
val mkString : Pstring.t -> t
val mkArray : EInstance.t * t array * t * t -> t

module UnsafeMonomorphic : sig
  val mkConst : Constant.t -> t
  val mkInd : inductive -> t
  val mkConstruct : constructor -> t
end

val mkConst : Constant.t -> t
[@@deprecated "(8.18) Use [mkConstU] or if truly needed [UnsafeMonomorphic.mkConst]"]

val mkInd : inductive -> t
[@@deprecated "(8.18) Use [mkIndU] or if truly needed [UnsafeMonomorphic.mkInd]"]

val mkConstruct : constructor -> t
[@@deprecated "(8.18) Use [mkConstructU] or if truly needed [UnsafeMonomorphic.mkConstruct]"]

val mkRef : GlobRef.t * EInstance.t -> t

val type1 : t

val applist : t * t list -> t
val applistc : t -> t list -> t

(** { Abstracting/generalizing over binders } *)

(** it = iterated
    or_LetIn = turn a local definition into a LetIn
    wo_LetIn = inlines local definitions (i.e. substitute them in the body)
    Named = binding is by name and the combinators turn it into a
            binding by index (complexity is nb(binders) * size(term)) *)

val it_mkProd : t -> (Name.t binder_annot * t) list -> t
val it_mkLambda : t -> (Name.t binder_annot * t) list -> t

val mkProd_or_LetIn : rel_declaration -> t -> t
val mkLambda_or_LetIn : rel_declaration -> t -> t
val it_mkProd_or_LetIn : t -> rel_context -> t
val it_mkLambda_or_LetIn : t -> rel_context -> t

val mkProd_wo_LetIn : rel_declaration -> t -> t
val mkLambda_wo_LetIn : rel_declaration -> t -> t
val it_mkProd_wo_LetIn : t -> rel_context -> t
val it_mkLambda_wo_LetIn : t -> rel_context -> t

val mkNamedProd : Evd.evar_map -> Id.t binder_annot -> types -> types -> types
val mkNamedLambda : Evd.evar_map -> Id.t binder_annot -> types -> constr -> constr
val mkNamedLetIn : Evd.evar_map -> Id.t binder_annot -> constr -> types -> constr -> constr

val mkNamedProd_or_LetIn : Evd.evar_map -> named_declaration -> types -> types
val mkNamedLambda_or_LetIn : Evd.evar_map -> named_declaration -> types -> types
val it_mkNamedProd_or_LetIn : Evd.evar_map -> t -> named_context -> t
val it_mkNamedLambda_or_LetIn : Evd.evar_map -> t -> named_context -> t

val mkNamedProd_wo_LetIn : Evd.evar_map -> named_declaration -> t -> t
val it_mkNamedProd_wo_LetIn : Evd.evar_map -> t -> named_context -> t

val mkLEvar : Evd.evar_map -> Evar.t * t list -> t
(** Variant of {!mkEvar} that removes identity variable instances from its argument. *)

(** {6 Simple case analysis} *)

val isRel  : Evd.evar_map -> t -> bool
val isVar  : Evd.evar_map -> t -> bool
val isInd  : Evd.evar_map -> t -> bool
val isRef : Evd.evar_map -> t -> bool
val isEvar : Evd.evar_map -> t -> bool
val isMeta : Evd.evar_map -> t -> bool
val isSort : Evd.evar_map -> t -> bool
val isCast : Evd.evar_map -> t -> bool
val isApp : Evd.evar_map -> t -> bool
val isLambda : Evd.evar_map -> t -> bool
val isLetIn : Evd.evar_map -> t -> bool
val isProd : Evd.evar_map -> t -> bool
val isConst : Evd.evar_map -> t -> bool
val isConstruct : Evd.evar_map -> t -> bool
val isFix : Evd.evar_map -> t -> bool
val isCoFix : Evd.evar_map -> t -> bool
val isCase : Evd.evar_map -> t -> bool
val isProj : Evd.evar_map -> t -> bool

val isType : Evd.evar_map -> constr -> bool

type arity = rel_context * ESorts.t
val mkArity : arity -> types
val destArity : Evd.evar_map -> types -> arity
val isArity : Evd.evar_map -> t -> bool

val isVarId  : Evd.evar_map -> Id.t -> t -> bool
val isRelN : Evd.evar_map -> int -> t -> bool
val isRefX : Environ.env -> Evd.evar_map -> GlobRef.t -> t -> bool

(** The string is interpreted by [Rocqlib.lib_ref]. If it is not registered, return [false]. *)
val is_lib_ref : Environ.env -> Evd.evar_map -> string -> t -> bool

val destRel : Evd.evar_map -> t -> int
val destMeta : Evd.evar_map -> t -> metavariable
val destVar : Evd.evar_map -> t -> Id.t
val destSort : Evd.evar_map -> t -> ESorts.t
val destCast : Evd.evar_map -> t -> t * cast_kind * t
val destProd : Evd.evar_map -> t -> Name.t binder_annot * types * types
val destLambda : Evd.evar_map -> t -> Name.t binder_annot * types * t
val destLetIn : Evd.evar_map -> t -> Name.t binder_annot * t * types * t
val destApp : Evd.evar_map -> t -> t * t array
val destConst : Evd.evar_map -> t -> Constant.t * EInstance.t
val destEvar : Evd.evar_map -> t -> t pexistential
val destInd : Evd.evar_map -> t -> inductive * EInstance.t
val destConstruct : Evd.evar_map -> t -> constructor * EInstance.t
val destCase : Evd.evar_map -> t -> case
val destProj : Evd.evar_map -> t -> Projection.t * ERelevance.t * t
val destFix : Evd.evar_map -> t -> (t, t, ERelevance.t) pfixpoint
val destCoFix : Evd.evar_map -> t -> (t, t, ERelevance.t) pcofixpoint

val destRef : Evd.evar_map -> t -> GlobRef.t * EInstance.t

val decompose_app : Evd.evar_map -> t -> t * t array
val decompose_app_list : Evd.evar_map -> t -> t * t list

(** Pops lambda abstractions until there are no more, skipping casts. *)
val decompose_lambda : Evd.evar_map -> t -> (Name.t binder_annot * t) list * t

(** Pops lambda abstractions and letins until there are no more, skipping casts. *)
val decompose_lambda_decls : Evd.evar_map -> t -> rel_context * t

(** Pops [n] lambda abstractions, skipping casts.

    @raise UserError if the term doesn't have enough lambdas. *)
val decompose_lambda_n : Evd.evar_map -> int -> t -> (Name.t binder_annot * t) list * t

(** Pops [n] lambda abstractions, and pop letins only if needed to
   expose enough lambdas, skipping casts.

    @raise UserError if the term doesn't have enough lambdas. *)
val decompose_lambda_n_assum : Evd.evar_map -> int -> t -> rel_context * t

(** Pops [n] lambda abstractions and letins, skipping casts.

     @raise UserError if the term doesn't have enough lambdas/letins. *)
val decompose_lambda_n_decls : Evd.evar_map -> int -> t -> rel_context * t

val prod_decls : Evd.evar_map -> t -> rel_context

val compose_lam : (Name.t binder_annot * t) list -> t -> t
[@@ocaml.deprecated "(8.17) Use [it_mkLambda] instead."]

val to_lambda : Evd.evar_map -> int -> t -> t

val decompose_prod : Evd.evar_map -> t -> (Name.t binder_annot * t) list * t
val decompose_prod_n : Evd.evar_map -> int -> t -> (Name.t binder_annot * t) list * t
val decompose_prod_decls : Evd.evar_map -> t -> rel_context * t
val decompose_prod_n_decls : Evd.evar_map -> int -> t -> rel_context * t

val existential_type : Evd.evar_map -> existential -> types
val whd_evar : Evd.evar_map -> constr -> constr

(** {6 Equality} *)

val eq_constr : Evd.evar_map -> t -> t -> bool
val eq_constr_nounivs : Evd.evar_map -> t -> t -> bool
val eq_constr_universes : Environ.env -> Evd.evar_map -> ?nargs:int -> t -> t -> UnivProblem.Set.t option
val leq_constr_universes : Environ.env -> Evd.evar_map -> ?nargs:int -> t -> t -> UnivProblem.Set.t option
val eq_existential : Evd.evar_map ->  (t -> t -> bool) -> existential -> existential -> bool

(** [eq_constr_universes_proj] can equate projections and their eta-expanded constant form. *)
val eq_constr_universes_proj : Environ.env -> Evd.evar_map -> t -> t -> UnivProblem.Set.t option

val compare_constr : Evd.evar_map -> (t -> t -> bool) -> t -> t -> bool

(** {6 Iterators} *)

val map : Evd.evar_map -> (t -> t) -> t -> t
val map_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> t) -> 'a -> t -> t
val map_branches : (t -> t) -> case_branch array -> case_branch array
val map_return_predicate : (t -> t) -> case_return -> case_return
val map_existential : Evd.evar_map -> (t -> t) -> existential -> existential
val iter : Evd.evar_map -> (t -> unit) -> t -> unit
val iter_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> unit) -> 'a -> t -> unit
val iter_with_full_binders : Environ.env -> Evd.evar_map -> (rel_declaration -> 'a -> 'a) -> ('a -> t -> unit) -> 'a -> t -> unit
val fold : Evd.evar_map -> ('a -> t -> 'a) -> 'a -> t -> 'a
val fold_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> 'b -> t -> 'b) -> 'a -> 'b -> t -> 'b

(** Gather the universes transitively used in the term, including in the
   type of evars appearing in it. *)
val universes_of_constr : ?init:Sorts.QVar.Set.t * Univ.Level.Set.t -> Evd.evar_map -> t -> Sorts.QVar.Set.t * Univ.Level.Set.t

(** {6 Substitutions} *)

module Vars :
sig

(** See vars.mli for the documentation of the functions below *)

type instance = t array
type instance_list = t list
type substl = t list

val lift : int -> t -> t
val liftn : int -> int -> t -> t
val substnl : substl -> int -> t -> t
val substl : substl -> t -> t
val subst1 : t -> t -> t

val substnl_decl : substl -> int -> rel_declaration -> rel_declaration
val substl_decl : substl -> rel_declaration -> rel_declaration
val subst1_decl : t -> rel_declaration -> rel_declaration

val replace_vars : Evd.evar_map -> (Id.t * t) list -> t -> t
val substn_vars : Evd.evar_map -> int -> Id.t list -> t -> t
val subst_vars : Evd.evar_map -> Id.t list -> t -> t
val subst_var : Evd.evar_map -> Id.t -> t -> t

val noccurn : Evd.evar_map -> int -> t -> bool
val noccur_between : Evd.evar_map -> int -> int -> t -> bool

val closedn : Evd.evar_map -> int -> t -> bool
val closed0 : Evd.evar_map -> t -> bool

val subst_univs_level_constr : UVars.sort_level_subst -> t -> t
val subst_instance_context : EInstance.t -> rel_context -> rel_context
val subst_instance_constr : EInstance.t -> t -> t
val subst_instance_relevance : EInstance.t -> ERelevance.t -> ERelevance.t

val subst_of_rel_context_instance : rel_context -> instance -> substl
val subst_of_rel_context_instance_list : rel_context -> instance_list -> substl

val liftn_rel_context : int -> int -> rel_context -> rel_context
val lift_rel_context : int -> rel_context -> rel_context
val substnl_rel_context : substl -> int -> rel_context -> rel_context
val substl_rel_context : substl -> rel_context -> rel_context
val smash_rel_context : rel_context -> rel_context

val esubst : (int -> 'a -> t) -> 'a Esubst.subs -> t -> t

type substituend
val make_substituend : t -> substituend
val lift_substituend : int -> substituend -> t

end

(** {5 Environment handling} *)

val push_rel : rel_declaration -> env -> env
val push_rel_context : rel_context -> env -> env
val push_rec_types : rec_declaration -> env -> env

val push_named : named_declaration -> env -> env
val push_named_context : named_context -> env -> env
val push_named_context_val  : named_declaration -> named_context_val -> named_context_val

val rel_context : env -> rel_context
val named_context : env -> named_context

val val_of_named_context : named_context -> named_context_val
val named_context_of_val : named_context_val -> named_context

val lookup_rel : int -> env -> rel_declaration
val lookup_named : variable -> env -> named_declaration
val lookup_named_val : variable -> named_context_val -> named_declaration

val map_rel_context_in_env :
  (env -> constr -> constr) -> env -> rel_context -> rel_context

val match_named_context_val :
  named_context_val -> (named_declaration * named_context_val) option

val identity_subst_val : named_context_val -> t SList.t

(* XXX Missing Sigma proxy *)
val fresh_global :
  ?loc:Loc.t -> ?rigid:Evd.rigid -> ?names:UVars.Instance.t -> Environ.env ->
  Evd.evar_map -> GlobRef.t -> Evd.evar_map * t

val is_global : Environ.env -> Evd.evar_map -> GlobRef.t -> t -> bool
[@@ocaml.deprecated "(8.12) Use [EConstr.isRefX] instead."]

val expand_case : Environ.env -> Evd.evar_map ->
  case -> (t,t,ERelevance.t) Inductive.pexpanded_case

val annotate_case : Environ.env -> Evd.evar_map -> case ->
  case_info * EInstance.t * t array * ((rel_context * t) * ERelevance.t) * case_invert * t * (rel_context * t) array
(** Same as above, but doesn't turn contexts into binders *)

val expand_branch : Environ.env -> Evd.evar_map ->
  EInstance.t -> t array -> constructor -> case_branch -> rel_context
(** Given a universe instance and parameters for the inductive type,
    constructs the typed context in which the branch lives. *)

val contract_case : Environ.env -> Evd.evar_map ->
  (t,t,ERelevance.t) Inductive.pexpanded_case -> case

(** {5 Extra} *)

val of_existential : Constr.existential -> existential
val of_named_decl : Constr.named_declaration -> named_declaration
val of_rel_decl : Constr.rel_declaration -> rel_declaration

val to_rel_decl : Evd.evar_map -> rel_declaration -> Constr.rel_declaration
val to_named_decl : Evd.evar_map -> named_declaration -> Constr.named_declaration

val of_named_context : Constr.named_context -> named_context
val of_rel_context : Constr.rel_context -> rel_context

val to_named_context : Evd.evar_map -> named_context -> Constr.named_context
val to_rel_context : Evd.evar_map -> rel_context -> Constr.rel_context

val of_case_invert : Constr.case_invert -> case_invert

val of_constr_array : Constr.t array -> t array

val of_binder_annot : 'a Constr.binder_annot -> 'a binder_annot

val to_binder_annot : Evd.evar_map -> 'a binder_annot -> 'a Constr.binder_annot

(** {5 Unsafe operations} *)

module Unsafe :
sig
  val to_constr : t -> Constr.t
  (** Physical identity. Does not care for defined evars. *)

  val to_constr_array : t array -> Constr.t array
  (** Physical identity. Does not care for defined evars. *)

  val to_binder_annot : 'a binder_annot -> 'a Constr.binder_annot

  val to_rel_decl : (t, types, ERelevance.t) Context.Rel.Declaration.pt ->
    (Constr.t, Constr.types, Sorts.relevance) Context.Rel.Declaration.pt
  (** Physical identity. Does not care for defined evars. *)

  val to_named_decl : (t, types, ERelevance.t) Context.Named.Declaration.pt ->
    (Constr.t, Constr.types, Sorts.relevance) Context.Named.Declaration.pt
  (** Physical identity. Does not care for defined evars. *)

  val to_named_context : (t, types, ERelevance.t) Context.Named.pt -> Constr.named_context

  val to_rel_context : (t, types, ERelevance.t) Context.Rel.pt -> Constr.rel_context

  val to_relevance : ERelevance.t -> Sorts.relevance

  val to_sorts : ESorts.t -> Sorts.t
  (** Physical identity. Does not care for normalization. *)

  val to_instance : EInstance.t -> UVars.Instance.t
  (** Physical identity. Does not care for normalization. *)

  val to_case_invert : case_invert -> Constr.case_invert

  val eq : (t, Constr.t) eq
  (** Use for transparent cast between types. *)

  val relevance_eq : (ERelevance.t, Sorts.relevance) eq
end

(** {5 Delayed evar expansion} *)

module Expand :
sig

type t
(** A variant of [EConstr.t] where evar substitution is performed on the fly.
    The [handle] type below is a kind of substitution that is needed to make
    sense of the delayed term. Such representation is more efficient than
    [EConstr.t] when iterating over a whole term.

    Caveat: the [kind] function below only returns the expanded head of the
    term. This means that when it returns [Evar (evk, inst)], [evk] is
    guaranteed to be undefined in the evar map but [inst] is, in general,
    not the same as you would get after expansion. You must call
    [expand_instance] before performing any operation on it. *)

type kind = (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term

type handle

val make : Evd.econstr -> handle * t
val repr : Evd.evar_map -> handle -> t -> Evd.econstr
val liftn_handle : int -> handle -> handle
val kind : Evd.evar_map -> handle -> t -> handle * kind
val expand_instance : skip:bool -> Evd.undefined Evd.evar_info -> handle -> t SList.t -> t SList.t
val iter : Evd.evar_map -> (handle -> t -> unit) -> handle -> kind -> unit
val iter_with_binders : Evd.evar_map ->
  ('a -> 'a) -> ('a -> handle -> t -> unit) -> 'a -> handle -> kind -> unit

end

(** Deprecated *)

val decompose_lambda_assum : Evd.evar_map -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_decls] instead."]
val decompose_prod_assum : Evd.evar_map -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_prod_decls] instead."]
val decompose_prod_n_assum : Evd.evar_map -> int -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_prod_n_decls] instead."]
val prod_assum : Evd.evar_map -> t -> rel_context
[@@ocaml.deprecated "(8.18) Use [prod_decls] instead."]

val decompose_lam : Evd.evar_map -> t -> (Name.t binder_annot * t) list * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda] instead."]
val decompose_lam_n_assum : Evd.evar_map -> int -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_n_assum] instead."]
val decompose_lam_n_decls : Evd.evar_map -> int -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_n_decls] instead."]
val decompose_lam_assum : Evd.evar_map -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_assum] instead."]
