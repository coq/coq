(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Locus
open Misctypes
open Tac2expr
open Tac2core
open Proofview.Notations

module Value = Tac2ffi

(** Standard tactics sharing their implementation with Ltac1 *)

let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let return x = Proofview.tclUNIT x
let v_unit = Value.of_unit ()

let lift tac = tac <*> return v_unit

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

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

let () = define_prim0 "tac_left" (Tactics.left_with_bindings false NoBindings)
let () = define_prim0 "tac_eleft" (Tactics.left_with_bindings true NoBindings)
let () = define_prim0 "tac_right" (Tactics.right_with_bindings false NoBindings)
let () = define_prim0 "tac_eright" (Tactics.right_with_bindings true NoBindings)

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

let () = define_prim1 "tac_constructorn" begin fun n ->
  let n = Value.to_int n in
  Tactics.constructor_tac false None n NoBindings
end

let () = define_prim1 "tac_econstructorn" begin fun n ->
  let n = Value.to_int n in
  Tactics.constructor_tac true None n NoBindings
end

let () = define_prim0 "tac_symmetry" (Tactics.intros_symmetry Locusops.onConcl)

let () = define_prim0 "tac_split" (Tactics.split_with_bindings false [NoBindings])
let () = define_prim0 "tac_esplit" (Tactics.split_with_bindings true [NoBindings])

let () = define_prim1 "tac_rename" begin fun ids ->
  let ids = Value.to_list ids in
  let map c = match Value.to_tuple c with
  | [|x; y|] -> (Value.to_ident x, Value.to_ident y)
  | _ -> assert false
  in
  let ids = List.map map ids in
  Tactics.rename_hyp ids
end

let () = define_prim1 "tac_revert" begin fun ids ->
  let ids = List.map Value.to_ident (Value.to_list ids) in
  Tactics.revert ids
end

let () = define_prim0 "tac_admit" Proofview.give_up

let () = define_prim2 "tac_fix" begin fun idopt n ->
  let idopt = Option.map Value.to_ident (Value.to_option idopt) in
  let n = Value.to_int n in
  Tactics.fix idopt n
end

let () = define_prim1 "tac_cofix" begin fun idopt ->
  let idopt = Option.map Value.to_ident (Value.to_option idopt) in
  Tactics.cofix idopt
end

let () = define_prim1 "tac_clear" begin fun ids ->
  let ids = List.map Value.to_ident (Value.to_list ids) in
  Tactics.clear ids
end

let () = define_prim1 "tac_keep" begin fun ids ->
  let ids = List.map Value.to_ident (Value.to_list ids) in
  Tactics.keep ids
end

let () = define_prim1 "tac_clearbody" begin fun ids ->
  let ids = List.map Value.to_ident (Value.to_list ids) in
  Tactics.clear_body ids
end

(** Tactics from extratactics *)

let () = define_prim1 "tac_absurd" begin fun c ->
  Contradiction.absurd (Value.to_constr c)
end

let () = define_prim1 "tac_subst" begin fun ids ->
  let ids = List.map Value.to_ident (Value.to_list ids) in
  Equality.subst ids
end

let () = define_prim0 "tac_substall" (return () >>= fun () -> Equality.subst_all ())
