(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Evd
open Pattern

(* arnaud: truc factices *)
type goal
type 'a sigma
(* arnaud: /truc factices *)

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

val match_with_forall_term    : (name * constr * constr) matching_function
val is_forall_term            : testing_function 

val match_with_imp_term    : (constr * constr) matching_function
val is_imp_term            : testing_function 

(* I added these functions to test whether a type contains dependent
  products or not, and if an inductive has constructors with dependent types
 (excluding parameters). this is useful to check whether a conjunction is a
 real conjunction and not a dependent tuple. (Pierre Corbineau, 13/5/2002) *)

val has_nodep_prod_after   : int -> testing_function
val has_nodep_prod         : testing_function

val match_with_nodep_ind   : (constr * constr list * int) matching_function  
val is_nodep_ind           : testing_function 

val match_with_sigma_type   : (constr * constr list) matching_function	  
val is_sigma_type           : testing_function 

(***** Destructing patterns bound to some theory *)

open Coqlib

(* Match terms [(eq A t u)] or [(identity A t u)] *)
(* Returns associated lemmas and [A,t,u] *)
val find_eq_data_decompose : constr -> 
  coq_leibniz_eq_data * (constr * constr * constr)

(* Match a term of the form [(existT A P t p)] *)
(* Returns associated lemmas and [A,P,t,p] *)
val find_sigma_data_decompose : constr -> 
  coq_sigma_data * (constr * constr * constr * constr)

(* Match a term of the form [{x:A|P}], returns [A] and [P] *)
val match_sigma : constr -> constr * constr

val is_matching_sigma : constr -> bool

(* Match a decidable equality judgement (e.g [{t=u:>T}+{~t=u}]), returns
   [t,u,T] and a boolean telling if equality is on the left side *)
val match_eqdec : constr -> bool * constr * constr * constr * constr

(* Match an equality up to conversion; returns [(eq,t1,t2)] in normal form *)
val dest_nf_eq : goal sigma -> constr -> (constr * constr * constr)

(* Match a negation *)
val is_matching_not : constr -> bool
val is_matching_imp_False : constr -> bool
