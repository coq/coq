(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

type types = t
type constr = t
type existential = t pexistential
type fixpoint = (t, t) pfixpoint
type cofixpoint = (t, t) pcofixpoint
type unsafe_judgment = (constr, types) Environ.punsafe_judgment
type unsafe_type_judgment = types Environ.punsafe_type_judgment
type named_declaration = (constr, types) Context.Named.Declaration.pt
type rel_declaration = (constr, types) Context.Rel.Declaration.pt
type named_context = (constr, types) Context.Named.pt
type rel_context = (constr, types) Context.Rel.pt

(** {5 Universe variables} *)

module ESorts :
sig
  type t
  (** Type of sorts up-to universe unification. Essentially a wrapper around
      Sorts.t so that normalization is ensured statically. *)

  val make : Sorts.t -> t
  (** Turn a sort into an up-to sort. *)

  val kind : Evd.evar_map -> t -> Sorts.t
  (** Returns the view into the current sort. Note that the kind of a variable
      may change if the unification state of the evar map changes. *)

end

module EInstance :
sig
  type t
  (** Type of universe instances up-to universe unification. Similar to
      {ESorts.t} for {Univ.Instance.t}. *)

  val make : Univ.Instance.t -> t
  val kind : Evd.evar_map -> t -> Univ.Instance.t
  val empty : t
  val is_empty : t -> bool
end

type 'a puniverses = 'a * EInstance.t

(** {5 Destructors} *)

val kind : Evd.evar_map -> t -> (t, t, ESorts.t, EInstance.t) Constr.kind_of_term
(** Same as {!Constr.kind} except that it expands evars and normalizes
    universes on the fly. *)

val kind_upto : Evd.evar_map -> Constr.t -> (Constr.t, Constr.t, Sorts.t, Univ.Instance.t) Constr.kind_of_term

val to_constr : ?abort_on_undefined_evars:bool -> Evd.evar_map -> t -> Constr.t
(** Returns the evar-normal form of the argument. Note that this
   function is supposed to be called when the original term has not
   more free-evars anymore. If you need compatibility with the old
   semantics, set [abort_on_undefined_evars] to [false].

    For getting the evar-normal form of a term with evars see
   {!Evarutil.nf_evar}. *)

val kind_of_type : Evd.evar_map -> t -> (t, t) Term.kind_of_type

(** {5 Constructors} *)

val of_kind : (t, t, ESorts.t, EInstance.t) Constr.kind_of_term -> t
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
val mkSort : Sorts.t -> t
val mkProp : t
val mkSet  : t
val mkType : Univ.Universe.t -> t
val mkCast : t * cast_kind * t -> t
val mkProd : Name.t * t * t -> t
val mkLambda : Name.t * t * t -> t
val mkLetIn : Name.t * t * t * t -> t
val mkApp : t * t array -> t
val mkConst : Constant.t -> t
val mkConstU : Constant.t * EInstance.t -> t
val mkProj : (Projection.t * t) -> t
val mkInd : inductive -> t
val mkIndU : inductive * EInstance.t -> t
val mkConstruct : constructor -> t
val mkConstructU : constructor * EInstance.t -> t
val mkConstructUi : (inductive * EInstance.t) * int -> t
val mkCase : case_info * t * t * t array -> t
val mkFix : (t, t) pfixpoint -> t
val mkCoFix : (t, t) pcofixpoint -> t
val mkArrow : t -> t -> t

val applist : t * t list -> t

val mkProd_or_LetIn : rel_declaration -> t -> t
val mkLambda_or_LetIn : rel_declaration -> t -> t
val it_mkProd_or_LetIn : t -> rel_context -> t
val it_mkLambda_or_LetIn : t -> rel_context -> t

val mkNamedLambda : Id.t -> types -> constr -> constr
val mkNamedLetIn : Id.t -> constr -> types -> constr -> constr
val mkNamedProd : Id.t -> types -> types -> types
val mkNamedLambda_or_LetIn : named_declaration -> types -> types
val mkNamedProd_or_LetIn : named_declaration -> types -> types

(** {6 Simple case analysis} *)

val isRel  : Evd.evar_map -> t -> bool
val isVar  : Evd.evar_map -> t -> bool
val isInd  : Evd.evar_map -> t -> bool
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
val destArity : Evd.evar_map -> types -> arity
val isArity : Evd.evar_map -> t -> bool

val isVarId  : Evd.evar_map -> Id.t -> t -> bool
val isRelN : Evd.evar_map -> int -> t -> bool

val destRel : Evd.evar_map -> t -> int
val destMeta : Evd.evar_map -> t -> metavariable
val destVar : Evd.evar_map -> t -> Id.t
val destSort : Evd.evar_map -> t -> ESorts.t
val destCast : Evd.evar_map -> t -> t * cast_kind * t
val destProd : Evd.evar_map -> t -> Name.t * types * types
val destLambda : Evd.evar_map -> t -> Name.t * types * t
val destLetIn : Evd.evar_map -> t -> Name.t * t * types * t
val destApp : Evd.evar_map -> t -> t * t array
val destConst : Evd.evar_map -> t -> Constant.t * EInstance.t
val destEvar : Evd.evar_map -> t -> t pexistential
val destInd : Evd.evar_map -> t -> inductive * EInstance.t
val destConstruct : Evd.evar_map -> t -> constructor * EInstance.t
val destCase : Evd.evar_map -> t -> case_info * t * t * t array
val destProj : Evd.evar_map -> t -> Projection.t * t
val destFix : Evd.evar_map -> t -> (t, t) pfixpoint
val destCoFix : Evd.evar_map -> t -> (t, t) pcofixpoint

val decompose_app : Evd.evar_map -> t -> t * t list

(** Pops lambda abstractions until there are no more, skipping casts. *)
val decompose_lam : Evd.evar_map -> t -> (Name.t * t) list * t

(** Pops lambda abstractions and letins until there are no more, skipping casts. *)
val decompose_lam_assum : Evd.evar_map -> t -> rel_context * t

(** Pops [n] lambda abstractions, and pop letins only if needed to
   expose enough lambdas, skipping casts.

    @raise UserError if the term doesn't have enough lambdas. *)
val decompose_lam_n_assum : Evd.evar_map -> int -> t -> rel_context * t

(** Pops [n] lambda abstractions and letins, skipping casts.

     @raise UserError if the term doesn't have enough lambdas/letins. *)
val decompose_lam_n_decls : Evd.evar_map -> int -> t -> rel_context * t

val compose_lam : (Name.t * t) list -> t -> t
val to_lambda : Evd.evar_map -> int -> t -> t

val decompose_prod : Evd.evar_map -> t -> (Name.t * t) list * t
val decompose_prod_assum : Evd.evar_map -> t -> rel_context * t
val decompose_prod_n_assum : Evd.evar_map -> int -> t -> rel_context * t

val existential_type : Evd.evar_map -> existential -> types
val whd_evar : Evd.evar_map -> constr -> constr

(** {6 Equality} *)

val eq_constr : Evd.evar_map -> t -> t -> bool
val eq_constr_nounivs : Evd.evar_map -> t -> t -> bool
val eq_constr_universes : Environ.env -> Evd.evar_map -> t -> t -> UnivProblem.Set.t option
val leq_constr_universes : Environ.env -> Evd.evar_map -> t -> t -> UnivProblem.Set.t option

(** [eq_constr_universes_proj] can equate projections and their eta-expanded constant form. *)
val eq_constr_universes_proj : Environ.env -> Evd.evar_map -> t -> t -> UnivProblem.Set.t option

val compare_constr : Evd.evar_map -> (t -> t -> bool) -> t -> t -> bool

(** {6 Iterators} *)

val map : Evd.evar_map -> (t -> t) -> t -> t
val map_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> t) -> 'a -> t -> t
val iter : Evd.evar_map -> (t -> unit) -> t -> unit
val iter_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> unit) -> 'a -> t -> unit
val iter_with_full_binders : Evd.evar_map -> (rel_declaration -> 'a -> 'a) -> ('a -> t -> unit) -> 'a -> t -> unit
val fold : Evd.evar_map -> ('a -> t -> 'a) -> 'a -> t -> 'a

(** Gather the universes transitively used in the term, including in the
   type of evars appearing in it. *)
val universes_of_constr : Evd.evar_map -> t -> Univ.LSet.t

(** {6 Substitutions} *)

module Vars :
sig

(** See vars.mli for the documentation of the functions below *)

type substl = t list

val lift : int -> t -> t
val liftn : int -> int -> t -> t
val substnl : substl -> int -> t -> t
val substl : substl -> t -> t
val subst1 : t -> t -> t

val substnl_decl : substl -> int -> rel_declaration -> rel_declaration
val substl_decl : substl -> rel_declaration -> rel_declaration
val subst1_decl : t -> rel_declaration -> rel_declaration

val replace_vars : (Id.t * t) list -> t -> t
val substn_vars : int -> Id.t list -> t -> t
val subst_vars : Id.t list -> t -> t
val subst_var : Id.t -> t -> t

val noccurn : Evd.evar_map -> int -> t -> bool
val noccur_between : Evd.evar_map -> int -> int -> t -> bool

val closedn : Evd.evar_map -> int -> t -> bool
val closed0 : Evd.evar_map -> t -> bool

val subst_univs_level_constr : Univ.universe_level_subst -> t -> t
val subst_of_rel_context_instance : rel_context -> t list -> t list


end

(** {5 Environment handling} *)

val push_rel : rel_declaration -> env -> env
val push_rel_context : rel_context -> env -> env
val push_rec_types : (t, t) Constr.prec_declaration -> env -> env

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

(* XXX Missing Sigma proxy *)
val fresh_global :
  ?loc:Loc.t -> ?rigid:Evd.rigid -> ?names:Univ.Instance.t -> Environ.env ->
  Evd.evar_map -> GlobRef.t -> Evd.evar_map * t

val is_global : Evd.evar_map -> GlobRef.t -> t -> bool

(** {5 Extra} *)

val of_existential : Constr.existential -> existential
val of_named_decl : (Constr.t, Constr.types) Context.Named.Declaration.pt -> (t, types) Context.Named.Declaration.pt
val of_rel_decl : (Constr.t, Constr.types) Context.Rel.Declaration.pt -> (t, types) Context.Rel.Declaration.pt

val to_rel_decl : Evd.evar_map -> (t, types) Context.Rel.Declaration.pt -> (Constr.t, Constr.types) Context.Rel.Declaration.pt

(** {5 Unsafe operations} *)

module Unsafe :
sig
  val to_constr : t -> Constr.t
  (** Physical identity. Does not care for defined evars. *)

  val to_rel_decl : (t, types) Context.Rel.Declaration.pt -> (Constr.t, Constr.types) Context.Rel.Declaration.pt
  (** Physical identity. Does not care for defined evars. *)

  val to_named_decl : (t, types) Context.Named.Declaration.pt -> (Constr.t, Constr.types) Context.Named.Declaration.pt
  (** Physical identity. Does not care for defined evars. *)

  val to_named_context : (t, types) Context.Named.pt -> Constr.named_context

  val to_sorts : ESorts.t -> Sorts.t
  (** Physical identity. Does not care for normalization. *)

  val to_instance : EInstance.t -> Univ.Instance.t
  (** Physical identity. Does not care for normalization. *)

  val eq : (t, Constr.t) eq
  (** Use for transparent cast between types. *)
end
