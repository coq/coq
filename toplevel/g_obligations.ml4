(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*
  Syntax for the subtac terms and types.
  Elaborated from correctness/psyntax.ml4 by Jean-Christophe Filliâtre *)


open Flags
open Util
open Names
open Nameops
open Vernacentries
open Reduction
open Term
open Libnames
open Topconstr

(* We define new entries for programs, with the use of this module
 * Subtac. These entries are named Subtac.<foo>
 *)

module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

module ObligationsGram =
struct
  let gec s = Gram.entry_create s

  let withtac : Tacexpr.raw_tactic_expr option Gram.entry = gec "withtac"
end

open Glob_term
open ObligationsGram
open Util
open Tok
open Pcoq
open Prim
open Constr

let sigref = mkRefC (Qualid (Pp.dummy_loc, Libnames.qualid_of_string "Coq.Init.Specif.sig"))

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

type 'a withtac_argtype = (Tacexpr.raw_tactic_expr option, 'a) Genarg.abstract_argument_type

let (wit_withtac : Genarg.tlevel withtac_argtype),
  (globwit_withtac : Genarg.glevel withtac_argtype),
  (rawwit_withtac : Genarg.rlevel withtac_argtype) =
  Genarg.create_arg None "withtac"

open Obligations

VERNAC COMMAND EXTEND Obligations
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

VERNAC COMMAND EXTEND Solve_Obligation
| [ "Solve" "Obligation" integer(num) "of" ident(name) "with" tactic(t) ] ->
    [ try_solve_obligation num (Some name) (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligation" integer(num) "with" tactic(t) ] ->
    [ try_solve_obligation num None (Some (Tacinterp.interp t)) ]
      END

VERNAC COMMAND EXTEND Solve_Obligations
| [ "Solve" "Obligations" "of" ident(name) "with" tactic(t) ] ->
    [ try_solve_obligations (Some name) (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligations" "with" tactic(t) ] ->
    [ try_solve_obligations None (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligations" ] ->
    [ try_solve_obligations None None ]
      END

VERNAC COMMAND EXTEND Solve_All_Obligations
| [ "Solve" "All" "Obligations" "with" tactic(t) ] ->
    [ solve_all_obligations (Some (Tacinterp.interp t)) ]
| [ "Solve" "All" "Obligations" ] ->
    [ solve_all_obligations None ]
      END

VERNAC COMMAND EXTEND Admit_Obligations
| [ "Admit" "Obligations" "of" ident(name) ] -> [ admit_obligations (Some name) ]
| [ "Admit" "Obligations" ] -> [ admit_obligations None ]
    END

VERNAC COMMAND EXTEND Set_Solver
| [ "Obligation" "Tactic" ":=" tactic(t) ] -> [
    set_default_tactic 
      (Vernacexpr.use_section_locality ())
      (Tacinterp.glob_tactic t) ]
END

open Pp

VERNAC COMMAND EXTEND Show_Solver
| [ "Show" "Obligation" "Tactic" ] -> [
    msgnl (str"Program obligation tactic is " ++ print_default_tactic ()) ]
END

VERNAC COMMAND EXTEND Show_Obligations
| [ "Obligations" "of" ident(name) ] -> [ show_obligations (Some name) ]
| [ "Obligations" ] -> [ show_obligations None ]
END

VERNAC COMMAND EXTEND Show_Preterm
| [ "Preterm" "of" ident(name) ] -> [ show_term (Some name) ]
| [ "Preterm" ] -> [ show_term None ]
END

open Pp

(* Declare a printer for the content of Program tactics *)
let () =
  let printer _ _ _ = function
  | None -> mt ()
  | Some tac -> str "with" ++ spc () ++ Pptactic.pr_raw_tactic (Global.env ()) tac
  in
  (* should not happen *)
  let dummy _ _ _ expr = assert false in
  Pptactic.declare_extra_genarg_pprule
    (rawwit_withtac, printer)
    (globwit_withtac, dummy)
    (wit_withtac, dummy)
