
(* $Id$ *)

(*i*)
open Pp
open Names
open Proof_trees
open Tacmach
open Term
(*i*)

(* Interpretation of tactics. *)

val cvt_arg              : Coqast.t -> tactic_arg

val tacinterp_add        : string * (tactic_arg list -> tactic) -> unit
val tacinterp_map        : string -> tactic_arg list -> tactic
val tacinterp_init       : unit -> unit
val interp               : Coqast.t -> tactic
val interp_atomic        : Coqast.loc -> string -> tactic_arg list -> tactic
val interp_semi_list     : tactic -> Coqast.t list -> tactic
val vernac_interp        : Coqast.t -> tactic
val vernac_interp_atomic : identifier -> tactic_arg list -> tactic
val overwriting_tacinterp_add : string * (tactic_arg list -> tactic) -> unit
val is_just_undef_macro     : Coqast.t -> string option

val bad_tactic_args : string -> 'a

