(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

(*
  Syntax for the subtac terms and types.
  Elaborated from correctness/psyntax.ml4 by Jean-Christophe Filliâtre *)


open Libnames
open Constrexpr
open Constrexpr_ops

(* We define new entries for programs, with the use of this module
 * Subtac. These entries are named Subtac.<foo>
 *)

module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

open Pcoq

let sigref = mkRefC (Qualid (Loc.ghost, Libnames.qualid_of_string "Coq.Init.Specif.sig"))

type 'a withtac_argtype = (Tacexpr.raw_tactic_expr option, 'a) Genarg.abstract_argument_type

let wit_withtac : Tacexpr.raw_tactic_expr option Genarg.uniform_genarg_type =
  Genarg.create_arg None "withtac"

let withtac = Pcoq.create_generic_entry "withtac" (Genarg.rawwit wit_withtac)

GEXTEND Gram
  GLOBAL: withtac;

  withtac:
    [ [ "with"; t = Tactic.tactic -> Some t
      | -> None ] ]
  ;

  Constr.closed_binder:
    [[ "("; id=Prim.name; ":"; t=Constr.lconstr; "|"; c=Constr.lconstr; ")" ->
	  let typ = mkAppC (sigref, [mkLambdaC ([id], default_binder_kind, t, c)]) in
          [LocalRawAssum ([id], default_binder_kind, typ)]
    ] ];

  END

open Obligations

let classify_obbl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND Obligations CLASSIFIED BY classify_obbl
| [ "Obligation" integer(num) "of" ident(name) ":" lconstr(t) withtac(tac) ] ->
    [ obligation (num, Some name, Some t) tac ]
| [ "Obligation" integer(num) "of" ident(name) withtac(tac) ] ->
    [ obligation (num, Some name, None) tac ]
| [ "Obligation" integer(num) ":" lconstr(t) withtac(tac) ] ->
    [ obligation (num, None, Some t) tac ]
| [ "Obligation" integer(num) withtac(tac) ] ->
    [ obligation (num, None, None) tac ]
| [ "Next" "Obligation" "of" ident(name) withtac(tac) ] ->
    [ next_obligation (Some name) tac ]
| [ "Next" "Obligation" withtac(tac) ] -> [ next_obligation None tac ]
END

VERNAC COMMAND EXTEND Solve_Obligation CLASSIFIED AS SIDEFF
| [ "Solve" "Obligation" integer(num) "of" ident(name) "with" tactic(t) ] ->
    [ try_solve_obligation num (Some name) (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligation" integer(num) "with" tactic(t) ] ->
    [ try_solve_obligation num None (Some (Tacinterp.interp t)) ]
END

VERNAC COMMAND EXTEND Solve_Obligations CLASSIFIED AS SIDEFF
| [ "Solve" "Obligations" "of" ident(name) "with" tactic(t) ] ->
    [ try_solve_obligations (Some name) (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligations" "with" tactic(t) ] ->
    [ try_solve_obligations None (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligations" ] ->
    [ try_solve_obligations None None ]
END

VERNAC COMMAND EXTEND Solve_All_Obligations CLASSIFIED AS SIDEFF
| [ "Solve" "All" "Obligations" "with" tactic(t) ] ->
    [ solve_all_obligations (Some (Tacinterp.interp t)) ]
| [ "Solve" "All" "Obligations" ] ->
    [ solve_all_obligations None ]
END

VERNAC COMMAND EXTEND Admit_Obligations CLASSIFIED AS SIDEFF
| [ "Admit" "Obligations" "of" ident(name) ] -> [ admit_obligations (Some name) ]
| [ "Admit" "Obligations" ] -> [ admit_obligations None ]
END

VERNAC COMMAND EXTEND Set_Solver CLASSIFIED AS SIDEFF
| [ "Obligation" "Tactic" ":=" tactic(t) ] -> [
    set_default_tactic
      (Locality.make_section_locality (Locality.LocalityFixme.consume ()))
      (Tacintern.glob_tactic t) ]
END

open Pp

VERNAC COMMAND EXTEND Show_Solver CLASSIFIED AS QUERY
| [ "Show" "Obligation" "Tactic" ] -> [
    msg_info (str"Program obligation tactic is " ++ print_default_tactic ()) ]
END

VERNAC COMMAND EXTEND Show_Obligations CLASSIFIED AS QUERY
| [ "Obligations" "of" ident(name) ] -> [ show_obligations (Some name) ]
| [ "Obligations" ] -> [ show_obligations None ]
END

VERNAC COMMAND EXTEND Show_Preterm CLASSIFIED AS QUERY
| [ "Preterm" "of" ident(name) ] -> [ msg_info (show_term (Some name)) ]
| [ "Preterm" ] -> [ msg_info (show_term None) ]
END

open Pp

(* Declare a printer for the content of Program tactics *)
let () =
  let printer _ _ _ = function
  | None -> mt ()
  | Some tac -> str "with" ++ spc () ++ Pptactic.pr_raw_tactic tac
  in
  (* should not happen *)
  let dummy _ _ _ expr = assert false in
  Pptactic.declare_extra_genarg_pprule wit_withtac printer dummy dummy
