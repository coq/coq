(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** A structure S is a non recursive inductive type with a single
   constructor *)
module Structure : sig

(** A projection to a structure field *)
type projection = {
  proj_name : Names.Name.t;            (** field name *)
  proj_true : bool;                    (** false = projection for a defined field (letin) *)
  proj_canonical : bool;               (** false = not to be used for CS inference *)
  proj_body : Names.Constant.t option; (** the projection function *)
}

type t = {
  name : Names.inductive;
  projections : projection list;
  nparams : int;
}

val make : Environ.env -> Names.inductive -> projection list -> t

val register : t -> unit
val subst : Mod_subst.substitution -> t -> t

(** refreshes nparams, e.g. after section discharging *)
val rebuild : Environ.env -> t -> t

(** [find isp] returns the Structure.t associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val find : Names.inductive -> t

(** raise [Not_found] if not a structure projection *)
val find_from_projection : Names.Constant.t -> t

(** [lookup_projections isp] returns the projections associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val find_projections : Names.inductive -> Names.Constant.t option list

(** raise [Not_found] if not a projection *)
val projection_nparams : Names.Constant.t -> int

val is_projection : Names.Constant.t -> bool

val projection_number : Environ.env -> Names.Constant.t -> int
(** [projection_number env p] returns the position of the projection p in
    the structure it corresponds to, counting from 0. *)

end

(** A canonical instance declares "canonical" conversion hints between
    the effective components of a structure and the projections of the
    structure *)
module Instance : sig

type t

(** Process a record instance, checkig it can be registered as canonical.
    The record type must be declared as a canonical Structure.t beforehand.  *)
val make : Environ.env -> Evd.evar_map -> Names.GlobRef.t -> t

(** Register an instance as canonical *)
val register : warn:bool -> Environ.env -> Evd.evar_map -> t -> unit

val subst : Mod_subst.substitution -> t -> t
val repr : t -> Names.GlobRef.t

end


(** A ValuePattern.t characterizes the form of a component of canonical
    instance and is used to query the data base of canonical instances *)
module ValuePattern : sig

type t =
  | Const_cs of Names.GlobRef.t
  | Proj_cs of Names.Projection.Repr.t
  | Prod_cs
  | Sort_cs of Sorts.family
  | Default_cs

val equal : Environ.env -> t -> t -> bool
val compare : t -> t -> int
val print : t -> Pp.t

(** Return the form of the component of a canonical structure *)
val of_constr : Evd.evar_map -> EConstr.t -> t * int option * EConstr.t list

end


(** The canonical solution of a problem (proj,val) is a global
    [constant = fun abs : abstractions_ty => body] and
    [body = RecodConstructor params canon_values] and the canonical value
    corresponding to val is [val cvalue_arguments].
    It is possible that val is one of the [abs] abstractions, eg [Default_cs],
    and in that case [cvalue_abstraction = Some i] *)
module CanonicalSolution : sig

type t = {
  constant : EConstr.t;

  abstractions_ty : EConstr.t list;
  body : EConstr.t;

  nparams : int;
  params : EConstr.t list;
  cvalue_abstraction : int option;
  cvalue_arguments : EConstr.t list;
}

(** [find (p,v)] returns a s such that p s = v.
    The solution s gets a fresh universe instance and is decomposed into
    bits for consumption by evarconv. Can raise [Not_found] on failure *)
val find :
  Environ.env -> Evd.evar_map -> (Names.GlobRef.t * ValuePattern.t) ->
    Evd.evar_map * t

(** [is_open_canonical_projection env sigma t] is true if t is a FieldName
    applied to term which is not a constructor. Used by evarconv not to
    unfold too much and lose a projection too early *)
val is_open_canonical_projection :
  ?metas:Reductionops.meta_handler ->
  Environ.env -> Evd.evar_map -> EConstr.t -> bool

val print : Environ.env -> Evd.evar_map -> t -> Pp.t

end

(** Low level access to the Canonical Structure database *)
module CSTable : sig

type entry = {
  projection : Names.GlobRef.t;
  value : ValuePattern.t;
  solution : Names.GlobRef.t;
}

(** [all] returns the list of tuples { p ; v ; s }
   Note: p s = v *)
val entries : unit -> entry list

(** [entries_for p] returns the list of canonical entries that have
    p as their FieldName *)
val entries_for : projection:Names.GlobRef.t -> entry list

end

(** Some extra info for structures which are primitive records *)
module PrimitiveProjections : sig

(** Sets up the mapping from constants to primitive projections *)
val register : Names.Projection.Repr.t -> Names.Constant.t -> unit

val mem : Names.Constant.t -> bool

val find_opt : Names.Constant.t -> Names.Projection.Repr.t option

val find_opt_with_relevance : Names.Constant.t * EConstr.EInstance.t
  -> (Names.Projection.Repr.t * EConstr.ERelevance.t) option

val is_transparent_constant : TransparentState.t -> Names.Constant.t -> bool
end
