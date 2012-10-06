(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tactics
open Util
open Locus
open Misctypes

(* Basic tactics *)
let h_intro_move = intro_move
let h_intro x = h_intro_move (Some x) MoveLast
let h_intros_until = intros_until
let h_assumption = assumption
let h_exact = exact_check
let h_exact_no_check = exact_no_check
let h_vm_cast_no_check = vm_cast_no_check
let h_apply = apply_with_bindings_gen
let h_apply_in simple ev cb (id,ipat) = apply_in simple ev id cb ipat
let h_elim = elim
let h_elim_type = elim_type
let h_case = general_case_analysis
let h_case_type = case_type
let h_fix = fix
let h_mutual_fix id n l = mutual_fix id n l 0

let h_cofix = cofix
let h_mutual_cofix id l = mutual_cofix id l 0

let h_cut = cut
let h_generalize_gen cl =
  generalize_gen (List.map (on_fst Redexpr.out_with_occurrences) cl)
let h_generalize cl =
  h_generalize_gen (List.map (fun c -> ((AllOccurrences,c),Names.Anonymous))
    cl)
let h_generalize_dep = generalize_dep
let h_let_tac b na c cl eqpat =
  let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
  let with_eq = if b then None else Some (true,id) in
  letin_tac with_eq na c None cl
let h_let_pat_tac b na c cl eqpat =
  let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
  let with_eq = if b then None else Some (true,id) in
  letin_pat_tac with_eq na c None cl

(* Derived basic tactics *)
let h_simple_induction_destruct isrec h =
  if isrec then (simple_induct h) else (simple_destruct h)
let h_simple_induction = h_simple_induction_destruct true
let h_simple_destruct = h_simple_induction_destruct false

let h_induction_destruct = induction_destruct
let h_new_induction ev c idl e cl =
  h_induction_destruct true ev ([c,idl],e,cl)
let h_new_destruct ev c idl e cl = h_induction_destruct false ev ([c,idl],e,cl)

let h_specialize = specialize
let h_lapply = cut_and_apply

(* Context management *)
let h_clear b l = (if b then keep else clear) l
let h_clear_body = clear_body
let h_move = move_hyp
let h_rename = rename_hyp
let h_revert = revert

(* Constructors *)
let h_left = left_with_bindings
let h_right = right_with_bindings
let h_split = split_with_bindings

let h_constructor ev n l = constructor_tac ev None n l
let h_one_constructor n = one_constructor n NoBindings
let h_simplest_left   = h_left false NoBindings
let h_simplest_right  = h_right false NoBindings

(* Conversion *)
let h_reduce = reduce
let h_change = change

(* Equivalence relations *)
let h_reflexivity = intros_reflexivity
let h_symmetry = intros_symmetry
let h_transitivity = intros_transitivity

let h_simplest_apply c = h_apply false false [Loc.ghost,(c,NoBindings)]
let h_simplest_eapply c = h_apply false true [Loc.ghost,(c,NoBindings)]
let h_simplest_elim c   = h_elim false (c,NoBindings) None
let h_simplest_case   c = h_case false (c,NoBindings)

let h_intro_patterns = intro_patterns

