(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Proof_type
(*i*)

(* This suppresses check done in [prim_refiner] for the tactic given in
   argument; works by side-effect *)

val with_check    : tactic -> tactic

(* [without_check] respectively means:\\
  [Intro]: no check that the name does not exist\\
  [Intro_after]: no check that the name does not exist and that variables in
     its type does not escape their scope\\
  [Intro_replacing]: no check that the name does not exist and that
     variables in its type does not escape their scope\\
  [Convert_hyp]:
  no check that the name exist and that its type is convertible\\
*)

(* The primitive refiner. *)

val prim_refiner : prim_rule -> evar_map -> goal -> goal list * evar_map

type proof_variable


val proof_variable_index : identifier -> proof_variable list -> int

(*s Refiner errors. *)

type refiner_error =

  (*i Errors raised by the refiner i*)
  | BadType of constr * constr * constr
  | UnresolvedBindings of name list
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr
  | MetaInType of constr

  (*i Errors raised by the tactics i*)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier

exception RefinerError of refiner_error

val catchable_exception : exn -> bool
