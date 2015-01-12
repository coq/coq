(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Names
open Misctypes
open Tacexpr
open Geninterp
open Quote

DECLARE PLUGIN "quote_plugin"

let loc = Loc.ghost
let cont = (loc, Id.of_string "cont")
let x = (loc, Id.of_string "x")

let make_cont (k : glob_tactic_expr) (c : Constr.t) =
  let c = Tacinterp.Value.of_constr c in
  let tac = TacCall (loc, ArgVar cont, [Reference (ArgVar x)]) in
  let tac = TacLetIn (false, [(cont, Tacexp k)], TacArg (loc, tac)) in
  let ist = { lfun = Id.Map.singleton (snd x) c; extra = TacStore.empty; } in
  Tacinterp.eval_tactic_ist ist tac

TACTIC EXTEND quote
  [ "quote" ident(f) ] -> [ quote f [] ]
| [ "quote" ident(f) "[" ne_ident_list(lc) "]"] -> [ quote f lc ]
| [ "quote" ident(f) "in" constr(c) "using" tactic(k) ] ->
  [ gen_quote (make_cont k) c f [] ]
| [ "quote" ident(f) "[" ne_ident_list(lc) "]"
    "in" constr(c) "using" tactic(k) ] ->
  [ gen_quote (make_cont k) c f lc ]
END
