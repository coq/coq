(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
(*i*)

(* Type errors. \label{typeerrors} *)

(*i Rem: NotEnoughAbstractionInFixBody should only occur with "/i" Fix
    notation i*)
type guard_error =
  (* Fixpoints *)
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType
  | RecursionOnIllegalTerm
  | NotEnoughArgumentsForFixCall
  (* CoFixpoints *)
  | CodomainNotInductiveType of constr
  | NestedRecursiveOccurrences
  | UnguardedRecursiveCall of constr
  | RecCallInTypeOfAbstraction of constr
  | RecCallInNonRecArgOfConstructor of constr
  | RecCallInTypeOfDef of constr
  | RecCallInCaseFun of constr
  | RecCallInCaseArg of constr
  | RecCallInCasePred of constr
  | NotGuardedForm

type type_error =
  | UnboundRel of int
  | NotAType of unsafe_judgment
  | BadAssumption of constr
  | ReferenceVariables of identifier
  | ElimArity of inductive * constr list * constr * unsafe_judgment
      * (constr * constr * string) option
  | CaseNotInductive of unsafe_judgment
  | NumberBranches of unsafe_judgment * int
  | IllFormedBranch of constr * int * constr * constr
  | Generalization of (name * types) * unsafe_judgment
  | ActualType of constr * constr * constr
  | CantApplyBadType of (int * constr * constr)
      * unsafe_judgment * unsafe_judgment list
  | CantApplyNonFunctional of unsafe_judgment * unsafe_judgment list
  | IllFormedRecBody of guard_error * name array * int * constr array
  | IllTypedRecBody of int * name array * unsafe_judgment array 
      * types array

exception TypeError of path_kind * env * type_error

val error_unbound_rel : path_kind -> env -> int -> 'a

val error_not_type : path_kind -> env -> unsafe_judgment -> 'a

val error_assumption : path_kind -> env -> constr -> 'a
 
val error_reference_variables : path_kind -> env -> identifier -> 'a

val error_elim_arity : 
  path_kind -> env -> inductive -> constr list -> constr 
    -> unsafe_judgment -> (constr * constr * string) option -> 'a

val error_case_not_inductive : 
  path_kind -> env -> unsafe_judgment -> 'a

val error_number_branches : 
  path_kind -> env -> unsafe_judgment -> int -> 'a

val error_ill_formed_branch :
  path_kind -> env -> constr -> int -> constr -> constr -> 'a

val error_generalization :
  path_kind -> env -> name * types -> unsafe_judgment -> 'a

val error_actual_type :
  path_kind -> env -> constr -> constr -> constr -> 'a

val error_cant_apply_not_functional : 
  path_kind -> env -> unsafe_judgment -> unsafe_judgment list -> 'a

val error_cant_apply_bad_type : 
  path_kind -> env -> int * constr * constr -> 
      unsafe_judgment -> unsafe_judgment list -> 'a

val error_ill_formed_rec_body :
  path_kind -> env -> guard_error -> name array -> int -> constr array -> 'a

val error_ill_typed_rec_body  :
  path_kind -> env -> int -> name array -> unsafe_judgment array 
    -> types array -> 'a

