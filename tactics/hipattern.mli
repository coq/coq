(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Evd
open Pattern
open Proof_trees
(*i*)

(*s Given a term with second-order variables in it,
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

val is_imp_term : constr -> bool

(*s I implemented the following functions which test whether a term [t]
   is an inductive but non-recursive type, a general conjuction, a
   general disjunction, or a type with no constructors.

   They are more general than matching with [or_term], [and_term], etc, 
   since they do not depend on the name of the type. Hence, they 
   also work on ad-hoc disjunctions introduced by the user.
   (Eduardo, 6/8/97). *)

type 'a matching_function = constr -> 'a option
type testing_function = constr -> bool

val match_with_non_recursive_type : (constr * constr list) matching_function
val is_non_recursive_type         : testing_function 

val match_with_disjunction : (constr * constr list) matching_function
val is_disjunction         : testing_function 

val match_with_conjunction : (constr * constr list) matching_function
val is_conjunction         : testing_function 

val match_with_empty_type  : constr matching_function
val is_empty_type          : testing_function 

val match_with_unit_type   : constr matching_function

(* type with only one constructor and no arguments *)
val is_unit_type           : testing_function 

val match_with_equation    : (constr * constr list) matching_function
val is_equation            : testing_function 

val match_with_nottype     : (constr * constr) matching_function
val is_nottype             : testing_function 
