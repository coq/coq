(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Locus
open Misctypes
open Genredexpr
open Tac2expr
open Tac2core
open Proofview.Notations

module Value = Tac2ffi

let to_pair f g = function
| ValBlk (0, [| x; y |]) -> (f x, g y)
| _ -> assert false

let to_name c = match Value.to_option Value.to_ident c with
| None -> Anonymous
| Some id -> Name id

let to_qhyp = function
| ValBlk (0, [| i |]) -> AnonHyp (Value.to_int i)
| ValBlk (1, [| id |]) -> NamedHyp (Value.to_ident id)
| _ -> assert false

let to_bindings = function
| ValInt 0 -> NoBindings
| ValBlk (0, [| vl |]) ->
  ImplicitBindings (Value.to_list Value.to_constr vl)
| ValBlk (1, [| vl |]) ->
  ExplicitBindings ((Value.to_list (fun p -> None, to_pair to_qhyp Value.to_constr p) vl))
| _ -> assert false

let to_constr_with_bindings = function
| ValBlk (0, [| c; bnd |]) -> (Value.to_constr c, to_bindings bnd)
| _ -> assert false

let to_int_or_var i = ArgArg (Value.to_int i)

let to_occurrences f = function
| ValInt 0 -> AllOccurrences
| ValBlk (0, [| vl |]) -> AllOccurrencesBut (Value.to_list f vl)
| ValInt 1 -> NoOccurrences
| ValBlk (1, [| vl |]) -> OnlyOccurrences (Value.to_list f vl)
| _ -> assert false

let to_hyp_location_flag = function
| ValInt 0 -> InHyp
| ValInt 1 -> InHypTypeOnly
| ValInt 2 -> InHypValueOnly
| _ -> assert false

let to_clause = function
| ValBlk (0, [| hyps; concl |]) ->
  let cast = function
  | ValBlk (0, [| hyp; occ; flag |]) ->
    ((to_occurrences to_int_or_var occ, Value.to_ident hyp), to_hyp_location_flag flag)
  | _ -> assert false
  in
  let hyps = Value.to_option (fun h -> Value.to_list cast h) hyps in
  { onhyps = hyps; concl_occs = to_occurrences to_int_or_var concl; }
| _ -> assert false

let to_evaluable_ref = function
| ValBlk (0, [| id |]) -> EvalVarRef (Value.to_ident id)
| ValBlk (1, [| cst |]) -> EvalConstRef (Value.to_constant cst)
| _ -> assert false

let to_red_flag = function
| ValBlk (0, [| beta; iota; fix; cofix; zeta; delta; const |]) ->
  {
    rBeta = Value.to_bool beta;
    rMatch = Value.to_bool iota;
    rFix = Value.to_bool fix;
    rCofix = Value.to_bool cofix;
    rZeta = Value.to_bool zeta;
    rDelta = Value.to_bool delta;
    rConst = Value.to_list to_evaluable_ref const;
  }
| _ -> assert false

let rec to_intro_pattern = function
| ValBlk (0, [| b |]) -> IntroForthcoming (Value.to_bool b)
| ValBlk (1, [| pat |]) -> IntroNaming (to_intro_pattern_naming pat)
| ValBlk (2, [| act |]) -> IntroAction (to_intro_pattern_action act)
| _ -> assert false

and to_intro_pattern_naming = function
| ValBlk (0, [| id |]) -> IntroIdentifier (Value.to_ident id)
| ValBlk (1, [| id |]) -> IntroFresh (Value.to_ident id)
| ValInt 0 -> IntroAnonymous
| _ -> assert false

and to_intro_pattern_action = function
| ValInt 0 -> IntroWildcard
| ValBlk (0, [| op |]) -> IntroOrAndPattern (to_or_and_intro_pattern op)
| ValBlk (1, [| inj |]) ->
  let map ipat = Loc.tag (to_intro_pattern ipat) in
  IntroInjection (Value.to_list map inj)
| ValBlk (2, [| _ |]) -> IntroApplyOn (assert false, assert false) (** TODO *)
| ValBlk (3, [| b |]) -> IntroRewrite (Value.to_bool b)
| _ -> assert false

and to_or_and_intro_pattern = function
| ValBlk (0, [| ill |]) ->
  IntroOrPattern (Value.to_list to_intro_patterns ill)
| ValBlk (1, [| il |]) ->
  IntroAndPattern (to_intro_patterns il)
| _ -> assert false

and to_intro_patterns il =
  let map ipat = Loc.tag (to_intro_pattern ipat) in
  Value.to_list map il

(** Standard tactics sharing their implementation with Ltac1 *)

let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let return x = Proofview.tclUNIT x
let v_unit = Value.of_unit ()

let lift tac = tac <*> return v_unit

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

let thaw f = Tac2interp.interp_app f [v_unit]

let define_prim0 name tac =
  let tac = function
  | [_] -> lift tac
  | _ -> assert false
  in
  Tac2env.define_primitive (pname name) tac

let define_prim1 name tac =
  let tac = function
  | [x] -> lift (tac x)
  | _ -> assert false
  in
  Tac2env.define_primitive (pname name) tac

let define_prim2 name tac =
  let tac = function
  | [x; y] -> lift (tac x y)
  | _ -> assert false
  in
  Tac2env.define_primitive (pname name) tac

let define_prim3 name tac =
  let tac = function
  | [x; y; z] -> lift (tac x y z)
  | _ -> assert false
  in
  Tac2env.define_primitive (pname name) tac

(** Tactics from Tacexpr *)

let () = define_prim1 "tac_intros" begin fun ipat ->
  let ipat = to_intro_patterns ipat in
  Tactics.intros_patterns false ipat
end

let () = define_prim1 "tac_eintros" begin fun ipat ->
  let ipat = to_intro_patterns ipat in
  Tactics.intros_patterns true ipat
end

let () = define_prim2 "tac_eelim" begin fun c copt ->
  let c = to_constr_with_bindings c in
  let copt = Value.to_option to_constr_with_bindings copt in
  Tactics.elim true None c copt
end

let () = define_prim1 "tac_ecase" begin fun c ->
  let c = to_constr_with_bindings c in
  Tactics.general_case_analysis true None c
end

let () = define_prim1 "tac_egeneralize" begin fun cl ->
  let cast = function
  | ValBlk (0, [| c; occs; na |]) ->
    ((to_occurrences Value.to_int occs, Value.to_constr c), to_name na)
  | _ -> assert false
  in
  let cl = Value.to_list cast cl in
  Tactics.new_generalize_gen cl
end

let () = define_prim3 "tac_assert" begin fun c tac ipat ->
  let c = Value.to_constr c in
  let of_tac t = Proofview.tclIGNORE (thaw t) in
  let tac = Value.to_option (fun t -> Value.to_option of_tac t) tac in
  let ipat = Value.to_option (fun ipat -> Loc.tag (to_intro_pattern ipat)) ipat in
  Tactics.forward true tac ipat c
end

let () = define_prim3 "tac_enough" begin fun c tac ipat ->
  let c = Value.to_constr c in
  let of_tac t = Proofview.tclIGNORE (thaw t) in
  let tac = Value.to_option (fun t -> Value.to_option of_tac t) tac in
  let ipat = Value.to_option (fun ipat -> Loc.tag (to_intro_pattern ipat)) ipat in
  Tactics.forward false tac ipat c
end

let () = define_prim2 "tac_pose" begin fun idopt c ->
  let na = to_name idopt in
  let c = Value.to_constr c in
  Tactics.letin_tac None na c None Locusops.nowhere
end

let () = define_prim3 "tac_set" begin fun idopt c cl ->
  let na = to_name idopt in
  let cl = to_clause cl in
  Proofview.tclEVARMAP >>= fun sigma ->
  thaw c >>= fun c ->
  let c = Value.to_constr c in
  Tactics.letin_pat_tac false None na (sigma, c) cl
end

let () = define_prim3 "tac_eset" begin fun idopt c cl ->
  let na = to_name idopt in
  let cl = to_clause cl in
  Proofview.tclEVARMAP >>= fun sigma ->
  thaw c >>= fun c ->
  let c = Value.to_constr c in
  Tactics.letin_pat_tac true None na (sigma, c) cl
end

let () = define_prim1 "tac_red" begin fun cl ->
  let cl = to_clause cl in
  Tactics.reduce (Red false) cl
end

let () = define_prim1 "tac_hnf" begin fun cl ->
  let cl = to_clause cl in
  Tactics.reduce Hnf cl
end

let () = define_prim2 "tac_cbv" begin fun flags cl ->
  let flags = to_red_flag flags in
  let cl = to_clause cl in
  Tactics.reduce (Cbv flags) cl
end

let () = define_prim2 "tac_cbn" begin fun flags cl ->
  let flags = to_red_flag flags in
  let cl = to_clause cl in
  Tactics.reduce (Cbn flags) cl
end

let () = define_prim2 "tac_lazy" begin fun flags cl ->
  let flags = to_red_flag flags in
  let cl = to_clause cl in
  Tactics.reduce (Lazy flags) cl
end

(** Tactics from coretactics *)

let () = define_prim0 "tac_reflexivity" Tactics.intros_reflexivity

(*

TACTIC EXTEND exact
  [ "exact" casted_constr(c) ] -> [ Tactics.exact_no_check c ]
END

*)

let () = define_prim0 "tac_assumption" Tactics.assumption

let () = define_prim1 "tac_transitivity" begin fun c ->
  let c = Value.to_constr c in
  Tactics.intros_transitivity (Some c)
end

let () = define_prim0 "tac_etransitivity" (Tactics.intros_transitivity None)

let () = define_prim1 "tac_cut" begin fun c ->
  let c = Value.to_constr c in
  Tactics.cut c
end

let () = define_prim1 "tac_left" begin fun bnd ->
  let bnd = to_bindings bnd in
  Tactics.left_with_bindings false bnd
end
let () = define_prim1 "tac_eleft" begin fun bnd ->
  let bnd = to_bindings bnd in
  Tactics.left_with_bindings true bnd
end
let () = define_prim1 "tac_right" begin fun bnd ->
  let bnd = to_bindings bnd in
  Tactics.right_with_bindings false bnd
end
let () = define_prim1 "tac_eright" begin fun bnd ->
  let bnd = to_bindings bnd in
  Tactics.right_with_bindings true bnd
end

let () = define_prim1 "tac_introsuntil" begin fun h ->
  Tactics.intros_until (to_qhyp h)
end

let () = define_prim1 "tac_exactnocheck" begin fun c ->
  Tactics.exact_no_check (Value.to_constr c)
end

let () = define_prim1 "tac_vmcastnocheck" begin fun c ->
  Tactics.vm_cast_no_check (Value.to_constr c)
end

let () = define_prim1 "tac_nativecastnocheck" begin fun c ->
  Tactics.native_cast_no_check (Value.to_constr c)
end

let () = define_prim0 "tac_constructor" (Tactics.any_constructor false None)
let () = define_prim0 "tac_econstructor" (Tactics.any_constructor true None)

let () = define_prim2 "tac_constructorn" begin fun n bnd ->
  let n = Value.to_int n in
  let bnd = to_bindings bnd in
  Tactics.constructor_tac false None n bnd
end

let () = define_prim2 "tac_econstructorn" begin fun n bnd ->
  let n = Value.to_int n in
  let bnd = to_bindings bnd in
  Tactics.constructor_tac true None n bnd
end

let () = define_prim1 "tac_symmetry" begin fun cl ->
  let cl = to_clause cl in
  Tactics.intros_symmetry cl
end

let () = define_prim1 "tac_split" begin fun bnd ->
  let bnd = to_bindings bnd in
  Tactics.split_with_bindings false [bnd]
end

let () = define_prim1 "tac_esplit" begin fun bnd ->
  let bnd = to_bindings bnd in
  Tactics.split_with_bindings true [bnd]
end

let () = define_prim1 "tac_rename" begin fun ids ->
  let map c = match Value.to_tuple c with
  | [|x; y|] -> (Value.to_ident x, Value.to_ident y)
  | _ -> assert false
  in
  let ids = Value.to_list map ids in
  Tactics.rename_hyp ids
end

let () = define_prim1 "tac_revert" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.revert ids
end

let () = define_prim0 "tac_admit" Proofview.give_up

let () = define_prim2 "tac_fix" begin fun idopt n ->
  let idopt = Value.to_option Value.to_ident idopt in
  let n = Value.to_int n in
  Tactics.fix idopt n
end

let () = define_prim1 "tac_cofix" begin fun idopt ->
  let idopt = Value.to_option Value.to_ident idopt in
  Tactics.cofix idopt
end

let () = define_prim1 "tac_clear" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.clear ids
end

let () = define_prim1 "tac_keep" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.keep ids
end

let () = define_prim1 "tac_clearbody" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.clear_body ids
end

(** Tactics from extratactics *)

let () = define_prim1 "tac_absurd" begin fun c ->
  Contradiction.absurd (Value.to_constr c)
end

let () = define_prim1 "tac_subst" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Equality.subst ids
end

let () = define_prim0 "tac_substall" (return () >>= fun () -> Equality.subst_all ())
