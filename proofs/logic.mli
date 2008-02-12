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
(* open Sign
open Evd
open Environ *)

(* [refine] tactic *)
val refine : Evd.open_constr -> Goal.tactic
(* [clear] tactic *)
val clear : identifier list -> Goal.tactic
(* [clearbody] tactic *)
val clear_body : identifier list -> Goal.tactic
(* [intro] tactic *)
val intro : identifier -> Goal.tactic

type simple_tactic =
  | Intro of identifier
  | Intro_replacing of identifier
  | Cut of bool * identifier * types
  | FixRule of identifier * int * (identifier * int * constr) list
  | Cofix of identifier * (identifier * constr) list
  | Refine of Evd.open_constr
  | Convert_concl of types * cast_kind 
  | Convert_hyp of named_declaration
  | Thin of identifier list
  | ThinBody of identifier list
  | Move of bool * identifier * identifier
  | Rename of identifier * identifier
  | Change_evars

val interprete_simple_tactic_as_single_tactic : simple_tactic -> Goal.tactic (* arnaud: type à changer *)

(*s Refiner errors. *)

type refiner_error =

  (*i Errors raised by the refiner i*)
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | OccurMetaGoal of constr
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr

  (*i Errors raised by the tactics i*)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier

exception RefinerError of refiner_error

(* arnaud: à commenter éventuellement*)
val catchable_exception : exn -> bool


(*** ***)
(* arnaud: trucs pour débugger *)


(*
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

val prim_extractor :
  (proof_variable list -> proof_tree -> constr)
  -> proof_variable list -> proof_tree -> constr

val proof_variable_index : identifier -> proof_variable list -> int

(*s Refiner errors. *)

type refiner_error =

  (*i Errors raised by the refiner i*)
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | OccurMetaGoal of constr
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr

  (*i Errors raised by the tactics i*)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier

exception RefinerError of refiner_error

val catchable_exception : exn -> bool
*)
