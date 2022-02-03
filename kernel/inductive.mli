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
    Raises an anomaly if the inductive type is not found. *)
val lookup_mind_specif : env -> inductive -> mind_specif

(** {6 Functions to build standard types related to inductive } *)

(** Returns the parameters of an inductive type with universes instantiated *)
val inductive_paramdecls : mutual_inductive_body puniverses -> Constr.rel_context

(** Returns the parameters of an inductive type with universes
    instantiated, splitting it into the contexts of recursively
    uniform and recursively non-uniform parameters *)
val inductive_nonrec_rec_paramdecls : mutual_inductive_body puniverses -> Constr.rel_context * Constr.rel_context

val instantiate_inductive_constraints :
  mutual_inductive_body -> Instance.t -> Constraints.t

type param_univs = (unit -> Sorts.t) list

val make_param_univs : Environ.env -> constr array -> param_univs
(** The constr array is the types of the arguments to a template
    polymorphic inductive. *)

val constrained_type_of_inductive : mind_specif puniverses -> types constrained
val constrained_type_of_inductive_knowing_parameters :
  mind_specif puniverses -> param_univs -> types constrained

val relevance_of_inductive : env -> inductive -> Sorts.relevance

val type_of_inductive : mind_specif puniverses -> types

val type_of_inductive_knowing_parameters :
  ?polyprop:bool -> mind_specif puniverses -> param_univs -> types

val elim_sort : mind_specif -> Sorts.family

val is_private : mind_specif -> bool
val is_primitive_record : mind_specif -> bool

(** Return type as quoted by the user *)

val constrained_type_of_constructor : pconstructor -> mind_specif -> types constrained
val type_of_constructor : pconstructor -> mind_specif -> types

(** Return constructor types in normal form *)
val arities_of_constructors : pinductive -> mind_specif -> types array

(** Return constructor types in user form *)
val type_of_constructors : pinductive -> mind_specif -> types array

(** Turns a constructor type recursively referring to inductive types
    into the same constructor type referring instead to a context made
    from the abstract declaration of the inductive types (e.g. turns
    [nat->nat] into [mkArrowR (Rel 1) (Rel 2)]); takes as arguments the number
    of inductive types in the block and the name of the block *)
val abstract_constructor_type_relatively_to_inductive_types_context :
  int -> MutInd.t -> types -> types

val inductive_params : mind_specif -> int

(** Given a pattern-matching represented compactly, expands it so as to produce
    lambda and let abstractions in front of the return clause and the pattern
    branches. *)
val expand_case : env -> case -> (case_info * constr * case_invert * constr * constr array)

val expand_case_specif : mutual_inductive_body -> case -> (case_info * constr * case_invert * constr * constr array)

(** Dual operation of the above. Fails if the return clause or branch has not
    the expected form. *)
val contract_case : env -> (case_info * constr * case_invert * constr * constr array) -> case

(** [instantiate_context u subst nas ctx] applies both [u] and [subst]
    to [ctx] while replacing names using [nas] (order reversed). In particular,
    assumes that [ctx] and [nas] have the same length. *)
val instantiate_context : Instance.t -> Vars.substl -> Name.t Context.binder_annot array ->
  rel_context -> rel_context

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
val check_case_info : env -> pinductive -> Sorts.relevance -> case_info -> unit

(** {6 Guard conditions for fix and cofix-points. } *)

(** [is_primitive_positive_container env c] tells if the constant [c] is
    registered as a primitive type that can be seen as a container where the
    occurrences of its parameters are positive, in which case the positivity and
    guard conditions are extended to allow inductive types to nest their subterms
    in these containers. *)
val is_primitive_positive_container : env -> Constant.t -> bool

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

val abstract_mind_lc : int -> int -> MutInd.t -> (rel_context * constr) array -> constr array
