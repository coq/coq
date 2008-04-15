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
open Proofview
(* open Sign
open Evd
open Environ *)

(*** [Goal.sensitive]-s: tool-kit for the tactic builder ***)
(* Raises Typing.type_of to the Goal monad *)
val type_of : constr -> types Goal.sensitive

(* type of [c] (in the expression monad), c must be well typed *)
val get_type_of : constr -> types Goal.sensitive

(* head normal form of the type of [c] (in the expression monad) *)
val hnf_type_of : constr -> types Goal.sensitive

(*** tacticals ***)

(* Tacticals from Proofview, for consistency *)
val tclTHEN : unit tactic -> 'a tactic -> 'a tactic
val tclBIND : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
val tclORELSE : unit tactic -> unit tactic -> unit tactic
val tclREPEAT : unit tactic -> unit tactic
val tclLIST : unit tactic list -> unit tactic
val tclEXTEND : unit tactic list -> 
                unit tactic -> 
                unit tactic list -> 
                unit tactic
val tclIGNORE : 'a tactic -> unit tactic

(* [do n] tactical *)
val tclDO : int -> unit tactic -> unit tactic
(* [try] tactical *)
val tclTRY : unit tactic -> unit tactic

(* [first] tactical *)
val tclFIRST : unit tactic list -> unit tactic

(* Wrapper tactical around tclLIST, takes an array as argument instead. *)
val tclARRAY : unit tactic array -> unit tactic

(* [tclTHENLIST [t1;...;tn]] and [tclTHENARRAY [| t1;...;tn |]] 
   apply t1 then ... then tn. *)
val tclTHENLIST : unit tactic list -> unit tactic
val tclTHENARRAY : unit tactic array -> unit tactic

(* [onLastHyp itac] applies [itac] to the name of the last
   hypothesis of the context *)
(* arnaud: statut ?*)
val onLastHyp : (identifier Goal.sensitive -> 'a tactic) 
                      -> 'a tactic

(*** tactics ***)
(* [refine] tactic *)
val refine : Goal.open_constr Goal.sensitive -> unit tactic
(* [clear] tactic *)
val clear : identifier list Goal.sensitive -> unit tactic
(* [clearbody] tactic *)
val clear_body : identifier list Goal.sensitive -> unit tactic
(* [intro] tactic *)
val intro : identifier Goal.sensitive -> unit tactic


(*** remettre dans [tactics] ?***)
(* [assumption] tactic *)
val assumption : unit tactic
(* [exact] tactic *)
val exact : Term.constr Goal.sensitive -> unit tactic
(* [apply] tactic *)
val apply_with_ebindings : 
          (Term.constr * Goal.open_constr Rawterm.bindings) Goal.sensitive
                  -> unit tactic
(* [eapply] tactic *)
val eapply_with_ebindings : 
          (Term.constr * Goal.open_constr Rawterm.bindings) Goal.sensitive 
                  -> unit tactic
(* [false] --> [apply] , [true] --> [eapply] *)
val apply_with_ebindings_gen : 
     bool -> (Term.constr * Goal.open_constr Rawterm.bindings) Goal.sensitive 
          -> unit tactic
(* [cut] tactic *)
val cut : Term.constr Goal.sensitive -> unit tactic

type simple_tactic =
  | Intro of identifier
  | Intro_replacing of identifier
  | Cut of bool * identifier * types
  | FixRule of identifier * int * (identifier * int * constr) list
  | Cofix of identifier * (identifier * constr) list
  | Refine of Goal.open_constr
  | Convert_concl of types * cast_kind 
  | Convert_hyp of named_declaration
  | Thin of identifier list
  | ThinBody of identifier list
  | Move of bool * identifier * identifier
  | Rename of identifier * identifier
  | Change_evars

(* arnaud: à virer sans doute ?
val interprete_simple_tactic_as_single_tactic : simple_tactic -> Goal.tactic (* arnaud: type à changer *)
*)

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
