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
open Proof_type
open Tacmach
open Genarg
open Tacexpr
open Rawterm
(*i*)

(* Tactics for the interpreter. They left a trace in the proof tree
   when they are called. *)

(* Basic tactics *)

val h_intro_move      : identifier option -> identifier option -> tactic
val h_intro           : identifier -> tactic
val h_intros_until    : quantified_hypothesis -> tactic

val h_assumption      : tactic
val h_exact           : constr -> tactic

val h_apply           : constr with_bindings -> tactic

val h_elim            : constr with_bindings ->
                        constr with_bindings option -> tactic
val h_elim_type       : constr -> tactic
val h_case            : constr with_bindings -> tactic
val h_case_type       : constr -> tactic

val h_mutual_fix      : identifier -> int ->
                        (identifier * int * constr) list -> tactic
val h_fix             : identifier option -> int -> tactic
val h_mutual_cofix    : identifier -> (identifier * constr) list -> tactic
val h_cofix           : identifier option -> tactic

val h_cut             : constr -> tactic 
val h_true_cut        : name -> constr -> tactic 
val h_generalize      : constr list -> tactic 
val h_generalize_dep  : constr -> tactic 
val h_forward         : bool -> name -> constr -> tactic 
val h_let_tac         : name -> constr -> Tacticals.clause -> tactic
val h_instantiate     : int -> constr -> Tacticals.clause -> tactic

(* Derived basic tactics *)

val h_simple_induction   : quantified_hypothesis * (bool ref * intro_pattern_expr list ref list) list ref -> tactic
val h_simple_destruct    : quantified_hypothesis -> tactic
val h_new_induction   :
  constr induction_arg -> constr with_bindings option ->
  intro_pattern_expr option * (bool ref * intro_pattern_expr list ref list) list ref
  -> tactic
val h_new_destruct    :
  constr induction_arg -> constr with_bindings option -> 
  intro_pattern_expr option * (bool ref * intro_pattern_expr list ref list) list ref
  -> tactic
val h_specialize      : int option -> constr with_bindings -> tactic
val h_lapply          : constr -> tactic

(* Automation tactic : see Auto *)


(* Context management *)
val h_clear           : identifier list -> tactic
val h_clear_body      : identifier list -> tactic
val h_move            : bool -> identifier -> identifier -> tactic
val h_rename          : identifier -> identifier -> tactic


(* Constructors *)
(*
val h_any_constructor : tactic -> tactic
*)
val h_constructor     : int -> constr bindings -> tactic
val h_left            : constr bindings -> tactic
val h_right           : constr bindings -> tactic
val h_split           : constr bindings -> tactic

val h_one_constructor : int -> tactic
val h_simplest_left   : tactic
val h_simplest_right  : tactic


(* Conversion *)
val h_reduce          : Tacred.red_expr -> Tacticals.clause -> tactic
val h_change          :
  constr occurrences option -> constr -> Tacticals.clause -> tactic

(* Equivalence relations *)
val h_reflexivity     : tactic
val h_symmetry        : Tacticals.clause -> tactic
val h_transitivity    : constr -> tactic

val h_simplest_apply  : constr -> tactic 
val h_simplest_elim   : constr -> tactic
val h_simplest_case   : constr -> tactic

val h_intro_patterns  : intro_pattern_expr list -> tactic
