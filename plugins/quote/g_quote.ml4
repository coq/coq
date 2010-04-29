(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Util
open Tacexpr
open Quote

let make_cont k x =
  let k = TacDynamic(dummy_loc, Tacinterp.tactic_in (fun _ -> fst k)) in
  let x = TacDynamic(dummy_loc, Pretyping.constr_in x) in
  let tac = <:tactic<let cont := $k in cont $x>> in
  Tacinterp.interp tac

TACTIC EXTEND quote
  [ "quote" ident(f) ] -> [ quote f [] ]
| [ "quote" ident(f) "[" ne_ident_list(lc) "]"] -> [ quote f lc ]
| [ "quote" ident(f) "in" constr(c) "using" tactic(k) ] ->
  [ gen_quote (make_cont k) c f [] ]
| [ "quote" ident(f) "[" ne_ident_list(lc) "]"
    "in" constr(c) "using" tactic(k) ] ->
  [ gen_quote (make_cont k) c f lc ]
END
