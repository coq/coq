(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Genarg
open Geninterp
open Ltac2_plugin
open Tac2val
open Tac2ffi
open Tac2expr
open Proofview.Notations
open Tac2externals

let ltac2_ltac1_plugin = "rocq-runtime.plugins.ltac2_ltac1"

let pname ?(plugin=ltac2_ltac1_plugin) s = { mltac_plugin = plugin; mltac_tactic = s }

let define ?plugin s = define (pname ?plugin s)

let val_tag wit = match val_tag wit with
| Base t -> t
| _ -> assert false

let prj : type a. a Val.typ -> Val.t -> a option = fun t v ->
  let Val.Dyn (t', x) = v in
  match Val.eq t t' with
  | None -> None
  | Some Refl -> Some x

let in_gen wit v = Val.Dyn (val_tag wit, v)

let out_gen wit v = prj (val_tag wit) v

let () =
  define "ltac1_of_intro_pattern" (Tac2stdlib.intro_pattern @-> ret Tac2quote_ltac1.ltac1) @@ fun v ->
  let v = Tac2tactics.mk_intro_pattern v in
  in_gen (topwit Ltac_plugin.Tacarg.wit_simple_intropattern) v

let rec to_intro_pattern (v : Tactypes.intro_pattern) : Tac2types.intro_pattern =
  match v.CAst.v with
  | IntroForthcoming b -> IntroForthcoming b
  | IntroNaming pat -> IntroNaming (to_intro_pattern_naming pat)
  | IntroAction act -> IntroAction (to_intro_pattern_action act)

(* these types have the same definition but aren't equal *)
and to_intro_pattern_naming : Namegen.intro_pattern_naming_expr -> Tac2types.intro_pattern_naming = function
  | IntroIdentifier id -> IntroIdentifier id
  | IntroFresh id -> IntroFresh id
  | IntroAnonymous -> IntroAnonymous

and to_intro_pattern_action : Tactypes.delayed_open_constr Tactypes.intro_pattern_action_expr -> Tac2types.intro_pattern_action = function
  | IntroWildcard -> IntroWildcard
  | IntroOrAndPattern op -> IntroOrAndPattern (to_or_and_intro_pattern op)
  | IntroInjection inj -> IntroInjection (to_intro_patterns inj)
  | IntroApplyOn ({loc;v=c}, ipat) ->
    let c =
      let open Proofview in
      Goal.enter_one ~__LOC__ @@ fun gl ->
      let sigma, c = c (Goal.env gl) (Goal.sigma gl) in
      Proofview.Unsafe.tclEVARS sigma >>= fun () ->
      tclUNIT (of_constr c)
    in
    let c = to_fun1 unit constr (mk_closure_val arity_one (fun _ -> c)) in
    IntroApplyOn (c, to_intro_pattern ipat)
  | IntroRewrite b -> IntroRewrite b

and to_or_and_intro_pattern : Tactypes.delayed_open_constr Tactypes.or_and_intro_pattern_expr -> Tac2types.or_and_intro_pattern = function
  | IntroOrPattern ill -> IntroOrPattern (List.map to_intro_patterns ill)
  | IntroAndPattern il -> IntroAndPattern (to_intro_patterns il)

and to_intro_patterns v = List.map to_intro_pattern v

let () =
  define "ltac1_to_intro_pattern" (Tac2quote_ltac1.ltac1 @-> ret (option Tac2stdlib.intro_pattern)) @@ fun v ->
  (* should we be using Taccoerce.coerce_to_intro_pattern instead?
     semantics are different: it also handles wit_hyp and Var constr *)
  match out_gen (topwit Ltac_plugin.Tacarg.wit_simple_intropattern) v with
  | None -> None
  | Some v ->
    let v = to_intro_pattern v in
    Some v
