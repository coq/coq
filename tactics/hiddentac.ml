(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Refiner
open Tacexpr
open Tactics
open Util
open Locus
open Misctypes

(* Basic tactics *)
let h_intro_move x y = abstract_tactic (intro_move x y)
let h_intro x        = h_intro_move (Some x) MoveLast
let h_intros_until x = abstract_tactic (intros_until x)
let h_assumption     = abstract_tactic assumption
let h_exact c        = abstract_tactic (exact_check c)
let h_exact_no_check c = abstract_tactic (exact_no_check c)
let h_vm_cast_no_check c = abstract_tactic (vm_cast_no_check c)
let h_apply simple ev cb = abstract_tactic
    (apply_with_bindings_gen simple ev cb)
let h_apply_in simple ev cb (id,ipat) =
  abstract_tactic (apply_in simple ev id cb ipat)
let h_elim ev cb cbo    = abstract_tactic (elim ev cb cbo)
let h_elim_type c    = abstract_tactic (elim_type c)
let h_case ev cb     = abstract_tactic (general_case_analysis ev cb)
let h_case_type c    = abstract_tactic (case_type c)
let h_fix ido n      = abstract_tactic (fix ido n)
let h_mutual_fix b id n l = abstract_tactic (mutual_fix id n l 0)

let h_cofix ido      = abstract_tactic (cofix ido)
let h_mutual_cofix b id l = abstract_tactic (mutual_cofix id l 0)

let h_cut c          = abstract_tactic (cut c)
let h_generalize_gen cl =
  abstract_tactic
    (generalize_gen (List.map (on_fst Redexpr.out_with_occurrences) cl))
let h_generalize cl =
  h_generalize_gen (List.map (fun c -> ((AllOccurrences,c),Names.Anonymous))
    cl)
let h_generalize_dep c =
  abstract_tactic (generalize_dep c)
let h_let_tac b na c cl eqpat =
  let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
  let with_eq = if b then None else Some (true,id) in
  abstract_tactic (letin_tac with_eq na c None cl)
let h_let_pat_tac b na c cl eqpat =
  let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
  let with_eq = if b then None else Some (true,id) in
  abstract_tactic (letin_pat_tac with_eq na c None cl)

(* Derived basic tactics *)
let h_simple_induction_destruct isrec h =
  abstract_tactic (if isrec then (simple_induct h) else (simple_destruct h))
let h_simple_induction = h_simple_induction_destruct true
let h_simple_destruct = h_simple_induction_destruct false

let h_induction_destruct isrec ev lcl =
  abstract_tactic (induction_destruct isrec ev lcl)
let h_new_induction ev c idl e cl =
  h_induction_destruct true ev ([c,idl],e,cl)
let h_new_destruct ev c idl e cl = h_induction_destruct false ev ([c,idl],e,cl)

let h_specialize n d = abstract_tactic (specialize n d)
let h_lapply c = abstract_tactic (cut_and_apply c)

(* Context management *)
let h_clear b l = abstract_tactic ((if b then keep else clear) l)
let h_clear_body l = abstract_tactic (clear_body l)
let h_move dep id1 id2 = abstract_tactic (move_hyp dep id1 id2)
let h_rename l = abstract_tactic (rename_hyp l)
let h_revert l = abstract_tactic (revert l)

(* Constructors *)
let h_left ev l  = abstract_tactic (left_with_bindings ev l)
let h_right ev l = abstract_tactic (right_with_bindings ev l)
let h_split ev l = abstract_tactic (split_with_bindings ev l)
(* Moved to tacinterp because of dependencies in Tacinterp.interp
let h_any_constructor t =
  abstract_tactic (TacAnyConstructor t) (any_constructor t)
*)
let h_constructor ev n l =
  abstract_tactic (constructor_tac ev None n l)
let h_one_constructor n =
  abstract_tactic (one_constructor n NoBindings)
let h_simplest_left   = h_left false NoBindings
let h_simplest_right  = h_right false NoBindings

(* Conversion *)
let h_reduce r cl  =
  abstract_tactic (reduce r cl)
let h_change op c cl =
  abstract_tactic (change op c cl)

(* Equivalence relations *)
let h_reflexivity    = abstract_tactic intros_reflexivity
let h_symmetry c     = abstract_tactic (intros_symmetry c)
let h_transitivity c = abstract_tactic (intros_transitivity c)

let h_simplest_apply c = h_apply false false [Loc.ghost,(c,NoBindings)]
let h_simplest_eapply c = h_apply false true [Loc.ghost,(c,NoBindings)]
let h_simplest_elim c   = h_elim false (c,NoBindings) None
let h_simplest_case   c = h_case false (c,NoBindings)

let h_intro_patterns l = abstract_tactic (intro_patterns l)

