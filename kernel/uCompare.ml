(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ

type conv_pb =
  | CONV
  | CUMUL

let pr_conv_pb = function
  | CUMUL -> Pp.str"≤"
  | CONV -> Pp.str"="


type ('a, 'err) convert_instances = UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err) Result.t
type ('a, 'err) convert_instances_cumul = conv_pb -> UVars.Variance.t array -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err) Result.t

type ('a, 'err) universe_compare = {
  compare_sorts : env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> ('a, 'err option) convert_instances;
  compare_cumul_instances : flex:bool -> ('a, 'err option) convert_instances_cumul;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare


let sort_cmp_universes env pb s0 s1 (u, check) =
  (check.compare_sorts env pb s0 s1 u, check)

(* [flex] should be true for constants, false for inductive types and
   constructors. *)
let convert_instances ~flex u u' (s, check) =
  (check.compare_instances ~flex u u' s, check)

exception MustExpand

let convert_instances_cumul ~flex pb var u u' (s, check) =
  (check.compare_cumul_instances ~flex pb var u u' s, check)

let get_cumulativity_constraints cv_pb variance u u' =
  match cv_pb with
  | CONV ->
    UVars.enforce_eq_variance_instances variance u u' Sorts.QUConstraints.empty
  | CUMUL ->
    UVars.enforce_leq_variance_instances variance u u' Sorts.QUConstraints.empty

let inductive_cumulativity_arguments (mind,ind) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs

let convert_inductives_gen cmp_instances cmp_cumul env cv_pb (mind, ind) ~nargs u1 u2 s =
  let mind = Environ.lookup_mind mind env in
  let ind = (mind, ind) in
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some variances ->
    let num_param_arity = inductive_cumulativity_arguments ind in
    if not (Int.equal num_param_arity nargs) then
      (* shortcut, not sure if worth doing, could use perf data *)
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      cmp_cumul cv_pb variances u1 u2 s

let convert_inductives env cv_pb ind ~nargs u1 u2 (s, check) =
  convert_inductives_gen (check.compare_instances ~flex:false)
    (check.compare_cumul_instances ~flex:false) env
    cv_pb ind ~nargs u1 u2 s, check

let constructor_cumulativity_arguments (mind, ind, ctor) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1)

let convert_constructors_gen cmp_instances cmp_cumul env ((mind, ind), cns) ~nargs u1 u2 s =
  let mind = Environ.lookup_mind mind env in
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some _ ->
    let num_cnstr_args = constructor_cumulativity_arguments (mind,ind,cns) in
    if not (Int.equal num_cnstr_args nargs) then
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      (** By invariant, both constructors have a common supertype,
          so they are convertible _at that type_. *)
      (* NB: no variance for qualities *)
      let variance = Array.make (snd (UVars.Instance.length u1)) UVars.Variance.Irrelevant in
      cmp_cumul CONV variance u1 u2 s

let convert_constructors env (ctor : Names.constructor) ~nargs u1 u2 (s, check) =
  convert_constructors_gen (check.compare_instances ~flex:false)
    (check.compare_cumul_instances ~flex:false) env
    ctor ~nargs u1 u2 s, check

let convert_constants_gen cmp_instances cmp_cumul env cv_pb cst ~nargs u1 u2 s =
  let cb = lookup_constant cst env in
  (match cb.Declarations.const_variance with
  | None -> cmp_instances u1 u2 s
  | Some variance ->
    let _foo = nargs in (* FIXME check nargs/variance compatibility *)
    let pri = UVars.Instance.pr Sorts.QVar.raw_pr (Univ.Universe.pr Univ.Level.raw_pr) in
    Feedback.msg_debug Pp.(str"conv_table_key: " ++ pri u1 ++ spc () ++ pr_conv_pb cv_pb ++ spc () ++ pri u2 ++ str" variances: " ++ UVars.pr_variances variance);
    cmp_cumul cv_pb variance u1 u2 s)

let convert_constants env cv_pb cst ~flex ~nargs u1 u2 (s, check) =
  convert_constants_gen (check.compare_instances ~flex)
  (check.compare_cumul_instances ~flex) env cv_pb cst ~nargs u1 u2 s, check
