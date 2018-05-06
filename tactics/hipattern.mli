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
open Evd
open EConstr
open Coqlib

(** High-order patterns *)

(** Given a term with second-order variables in it,
   represented by Meta's, and possibly applied using SoApp
   terms, this function will perform second-order, binding-preserving,
   matching, in the case where the pattern is a pattern in the sense
   of Dale Miller.

   ALGORITHM:

   Given a pattern, we decompose it, flattening casts and apply's,
   recursing on all operators, and pushing the name of the binder each
   time we descend a binder.

   When we reach a first-order variable, we ask that the corresponding
   term's free-rels all be higher than the depth of the current stack.

   When we reach a second-order application, we ask that the
   intersection of the free-rels of the term and the current stack be
   contained in the arguments of the application *)

(** I implemented the following functions which test whether a term [t]
   is an inductive but non-recursive type, a general conjuction, a
   general disjunction, or a type with no constructors.

   They are more general than matching with [or_term], [and_term], etc,
   since they do not depend on the name of the type. Hence, they
   also work on ad-hoc disjunctions introduced by the user.
   (Eduardo, 6/8/97). *)

type 'a matching_function = evar_map -> constr -> 'a option
type testing_function = evar_map -> constr -> bool

val match_with_non_recursive_type : (constr * constr list) matching_function
val is_non_recursive_type         : testing_function

(** Non recursive type with no indices and exactly one argument for each
   constructor; canonical definition of n-ary disjunction if strict *)
val match_with_disjunction : ?strict:bool -> ?onlybinary:bool -> (constr * constr list) matching_function
val is_disjunction         : ?strict:bool -> ?onlybinary:bool -> testing_function

(** Non recursive tuple (one constructor and no indices) with no inner
   dependencies; canonical definition of n-ary conjunction if strict *)
val match_with_conjunction : ?strict:bool -> ?onlybinary:bool -> (constr * constr list) matching_function
val is_conjunction         : ?strict:bool -> ?onlybinary:bool -> testing_function

(** Non recursive tuple, possibly with inner dependencies *)
val match_with_record      : (constr * constr list) matching_function
val is_record              : testing_function

(** Like record but supports and tells if recursive (e.g. Acc) *)
val match_with_tuple       : (constr * constr list * bool) matching_function
val is_tuple               : testing_function

(** No constructor, possibly with indices *)
val match_with_empty_type  : constr matching_function
val is_empty_type          : testing_function

(** type with only one constructor and no arguments, possibly with indices *)
val match_with_unit_or_eq_type : constr matching_function
val is_unit_or_eq_type     : testing_function

(** type with only one constructor and no arguments, no indices *)
val is_unit_type           : testing_function

(** type with only one constructor, no arguments and at least one dependency *)
val is_inductive_equality  : inductive -> bool
val match_with_equality_type : (constr * constr list) matching_function
val is_equality_type       : testing_function

val match_with_nottype     : Environ.env -> (constr * constr) matching_function
val is_nottype             : Environ.env -> testing_function

val match_with_forall_term    : (Name.t * constr * constr) matching_function
val is_forall_term            : testing_function

val match_with_imp_term    : (constr * constr) matching_function
val is_imp_term            : testing_function

(** I added these functions to test whether a type contains dependent
  products or not, and if an inductive has constructors with dependent types
 (excluding parameters). this is useful to check whether a conjunction is a
 real conjunction and not a dependent tuple. (Pierre Corbineau, 13/5/2002) *)

val has_nodep_prod_after   : int -> testing_function
val has_nodep_prod         : testing_function

val match_with_nodep_ind   : (constr * constr list * int) matching_function
val is_nodep_ind           : testing_function

val match_with_sigma_type   : (constr * constr list) matching_function
val is_sigma_type           : testing_function

(** Recongnize inductive relation defined by reflexivity *)

type equation_kind =
  | MonomorphicLeibnizEq of constr * constr
  | PolymorphicLeibnizEq of constr * constr * constr
  | HeterogenousEq of constr * constr * constr * constr

exception NoEquationFound

val match_with_equation:
  Environ.env -> evar_map -> constr -> coq_eq_data option * constr * equation_kind

(***** Destructing patterns bound to some theory *)

(** Match terms [eq A t u], [identity A t u] or [JMeq A t A u] 
   Returns associated lemmas and [A,t,u] or fails PatternMatchingFailure *)
val find_eq_data_decompose : Proofview.Goal.t -> constr ->
      coq_eq_data * EInstance.t * (types * constr * constr)

(** Idem but fails with an error message instead of PatternMatchingFailure *)
val find_this_eq_data_decompose : Proofview.Goal.t -> constr ->
      coq_eq_data * EInstance.t * (types * constr * constr)

(** A variant that returns more informative structure on the equality found *)
val find_eq_data : evar_map -> constr -> coq_eq_data * EInstance.t * equation_kind

(** Match a term of the form [(existT A P t p)] 
   Returns associated lemmas and [A,P,t,p] *)
val find_sigma_data_decompose : Environ.env -> evar_map -> constr ->
  coq_sigma_data * (EInstance.t * constr * constr * constr * constr)

(** Match a term of the form [{x:A|P}], returns [A] and [P] *)
val match_sigma : Environ.env -> evar_map -> constr -> constr * constr

val is_matching_sigma : Environ.env -> evar_map -> constr -> bool

(** Match a decidable equality judgement (e.g [{t=u:>T}+{~t=u}]), returns
   [t,u,T] and a boolean telling if equality is on the left side *)
val match_eqdec : Environ.env -> evar_map -> constr -> bool * GlobRef.t * constr * constr * constr

(** Match a negation *)
val is_matching_not : Environ.env -> evar_map -> constr -> bool
val is_matching_imp_False : Environ.env -> evar_map -> constr -> bool
