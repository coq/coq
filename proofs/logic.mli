
(* $Id$ *)

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

val without_check : tactic -> tactic

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

val prim_refiner : prim_rule -> 'a evar_map -> goal -> goal list

val prim_extractor :
  (identifier list -> proof_tree -> constr)
  -> identifier list -> proof_tree -> constr

(*s Refiner errors. *)

type refiner_error =
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | CannotApply of constr * constr
  | CannotUnify of constr * constr
  | CannotGeneralize of constr
  | NotWellTyped of constr
  | BadTacticArgs of string * tactic_arg list
  | IntroNeedsProduct

exception RefinerError of refiner_error

val error_cannot_unify : path_kind -> constr * constr -> 'a

val catchable_exception : exn -> bool


(*s Pretty-printer. *)

val pr_prim_rule   : prim_rule -> Pp.std_ppcmds
