
(*i $Id$ i*)

(*i*)
open Proof_type
open Tacmach
(*i*)

(* Registered tactics. *)

val v_absurd        : tactic_arg list -> tactic
val v_contradiction : tactic_arg list -> tactic
val v_reflexivity   : tactic_arg list -> tactic
val v_symmetry      : tactic_arg list -> tactic
val v_transitivity  : tactic_arg list -> tactic
val v_intro         : tactic_arg list -> tactic
val v_introsUntil   : tactic_arg list -> tactic
(*i val v_tclIDTAC      : tactic_arg list -> tactic i*)
val v_assumption    : tactic_arg list -> tactic
val v_exact         : tactic_arg list -> tactic
val v_reduce        : tactic_arg list -> tactic
val v_constructor   : tactic_arg list -> tactic
val v_left          : tactic_arg list -> tactic
val v_right         : tactic_arg list -> tactic
val v_split         : tactic_arg list -> tactic
val v_clear         : tactic_arg list -> tactic
val v_move          : tactic_arg list -> tactic
val v_move_dep      : tactic_arg list -> tactic
val v_apply         : tactic_arg list -> tactic
val v_cutAndResolve : tactic_arg list -> tactic
val v_cut           : tactic_arg list -> tactic
val v_lettac        : tactic_arg list -> tactic
val v_generalize    : tactic_arg list -> tactic
val v_generalize_dep : tactic_arg list -> tactic
val v_specialize    : tactic_arg list -> tactic
val v_elim          : tactic_arg list -> tactic
val v_elimType      : tactic_arg list -> tactic
val v_induction     : tactic_arg list -> tactic
val v_case          : tactic_arg list -> tactic
val v_caseType      : tactic_arg list -> tactic
val v_destruct      : tactic_arg list -> tactic
val v_fix           : tactic_arg list -> tactic
val v_cofix         : tactic_arg list -> tactic
