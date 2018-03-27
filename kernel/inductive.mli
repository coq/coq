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
open Constr
open Univ
open Declarations
open Environ

(** {6 Extracting an inductive type from a construction } *)

(** [find_m*type env sigma c] coerce [c] to an recursive type (I args).
   [find_rectype], [find_inductive] and [find_coinductive]
   respectively accepts any recursive type, only an inductive type and
   only a coinductive type.
   They raise [Not_found] if not convertible to a recursive type. *)

val find_rectype     : env -> types -> pinductive * constr list
val find_inductive   : env -> types -> pinductive * constr list
val find_coinductive : env -> types -> pinductive * constr list

type mind_specif = mutual_inductive_body * one_inductive_body

(** {6 ... } *)
(** Fetching information in the environment about an inductive type.
    Raises [Not_found] if the inductive type is not found. *)
val lookup_mind_specif : env -> inductive -> mind_specif

(** {6 Functions to build standard types related to inductive } *)
val ind_subst : MutInd.t -> mutual_inductive_body -> Instance.t -> constr list

val inductive_paramdecls : mutual_inductive_body puniverses -> Constr.rel_context

val instantiate_inductive_constraints :
  mutual_inductive_body -> Instance.t -> Constraint.t

val constrained_type_of_inductive : env -> mind_specif puniverses -> types constrained
val constrained_type_of_inductive_knowing_parameters :
  env -> mind_specif puniverses -> types Lazy.t array -> types constrained

val type_of_inductive : env -> mind_specif puniverses -> types

val type_of_inductive_knowing_parameters :
  env -> ?polyprop:bool -> mind_specif puniverses -> types Lazy.t array -> types

val elim_sorts : mind_specif -> Sorts.family list

val is_private : mind_specif -> bool
val is_primitive_record : mind_specif -> bool

(** Return type as quoted by the user *)

val constrained_type_of_constructor : pconstructor -> mind_specif -> types constrained
val type_of_constructor : pconstructor -> mind_specif -> types

(** Return constructor types in normal form *)
val arities_of_constructors : pinductive -> mind_specif -> types array

(** Return constructor types in user form *)
val type_of_constructors : pinductive -> mind_specif -> types array

(** Transforms inductive specification into types (in nf) *)
val arities_of_specif : MutInd.t puniverses -> mind_specif -> types array

val inductive_params : mind_specif -> int

(** [type_case_branches env (I,args) (p:A) c] computes useful types
   about the following Cases expression:
      <p>Cases (c :: (I args)) of b1..bn end
   It computes the type of every branch (pattern variables are
   introduced by products), the type for the whole expression, and
   the universe constraints generated.
 *)
val type_case_branches :
  env -> pinductive * constr list -> unsafe_judgment -> constr
    -> types array * types

val build_branches_type :
  pinductive -> mutual_inductive_body * one_inductive_body ->
    constr list -> constr -> types array

(** Return the arity of an inductive type *)
val mind_arity : one_inductive_body -> Constr.rel_context * Sorts.family

val inductive_sort_family : one_inductive_body -> Sorts.family

(** Check a [case_info] actually correspond to a Case expression on the
   given inductive type. *)
val check_case_info : env -> pinductive -> case_info -> unit

(** {6 Guard conditions for fix and cofix-points. } *)

(** When [chk] is false, the guard condition is not actually
    checked. *)
val check_fix : env -> fixpoint -> unit
val check_cofix : env -> cofixpoint -> unit

(** {6 Support for sort-polymorphic inductive types } *)

(** The "polyprop" optional argument below controls
    the "Prop-polymorphism". By default, it is allowed.
    But when "polyprop=false", the following exception is raised
    when a polymorphic singleton inductive type becomes Prop due to
    parameter instantiation. This is used by the Ocaml extraction,
    which cannot handle (yet?) Prop-polymorphism. *)

exception SingletonInductiveBecomesProp of Id.t

val max_inductive_sort : Sorts.t array -> Universe.t

val instantiate_universes : env -> Constr.rel_context ->
  template_arity -> constr Lazy.t array -> Constr.rel_context * Sorts.t

(** {6 Debug} *)

type size = Large | Strict
type subterm_spec =
    Subterm of (size * wf_paths)
  | Dead_code
  | Not_subterm
type guard_env =
  { env     : env;
    (** dB of last fixpoint *)
    rel_min : int;
    (** dB of variables denoting subterms *)
    genv    : subterm_spec Lazy.t list;
  }

type stack_element = |SClosure of guard_env*constr |SArg of subterm_spec Lazy.t

val subterm_specif : guard_env -> stack_element list -> constr -> subterm_spec

val lambda_implicit_lift : int -> constr -> constr

val abstract_mind_lc : int -> Int.t -> constr array -> constr array
