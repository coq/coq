(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)


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

module SubtacGram =
struct
  let gec s = Gram.Entry.create ("Subtac."^s)
		(* types *)
  let subtac_gallina_loc : Vernacexpr.vernac_expr located Gram.Entry.e = gec "subtac_gallina_loc"

  let subtac_withtac : Tacexpr.raw_tactic_expr option Gram.Entry.e = gec "subtac_withtac"
end

open Rawterm
open SubtacGram
open Util
open Pcoq
open Prim
open Constr
let sigref = mkRefC (Qualid (dummy_loc, Libnames.qualid_of_string "Coq.Init.Specif.sig"))

GEXTEND Gram
  GLOBAL: subtac_gallina_loc typeclass_constraint Constr.binder subtac_withtac;

  subtac_gallina_loc:
    [ [ g = Vernac.gallina -> loc, g
    | g = Vernac.gallina_ext -> loc, g ] ]
    ;

  subtac_withtac:
    [ [ "with"; t = Tactic.tactic -> Some t
      | -> None ] ]
  ;

  Constr.binder_let:
    [[ "("; id=Prim.name; ":"; t=Constr.lconstr; "|"; c=Constr.lconstr; ")" ->
	  let typ = mkAppC (sigref, [mkLambdaC ([id], default_binder_kind, t, c)]) in
          [LocalRawAssum ([id], default_binder_kind, typ)]
    ] ];

  Constr.binder:
    [ [ "("; id=Prim.name; ":"; c=Constr.lconstr; "|"; p=Constr.lconstr; ")" ->
          ([id],default_binder_kind, mkAppC (sigref, [mkLambdaC ([id], default_binder_kind, c, p)]))
      | "("; id=Prim.name; ":"; c=Constr.lconstr; ")" ->
          ([id],default_binder_kind, c)
      | "("; id=Prim.name; lid=LIST1 Prim.name; ":"; c=Constr.lconstr; ")" ->
          (id::lid,default_binder_kind, c)
    ] ];

  END


type 'a gallina_loc_argtype = (Vernacexpr.vernac_expr located, 'a) Genarg.abstract_argument_type

let (wit_subtac_gallina_loc : Genarg.tlevel gallina_loc_argtype),
  (globwit_subtac_gallina_loc : Genarg.glevel gallina_loc_argtype),
  (rawwit_subtac_gallina_loc : Genarg.rlevel gallina_loc_argtype) =
  Genarg.create_arg "subtac_gallina_loc"

type 'a withtac_argtype = (Tacexpr.raw_tactic_expr option, 'a) Genarg.abstract_argument_type

let (wit_subtac_withtac : Genarg.tlevel withtac_argtype),
  (globwit_subtac_withtac : Genarg.glevel withtac_argtype),
  (rawwit_subtac_withtac : Genarg.rlevel withtac_argtype) =
  Genarg.create_arg "subtac_withtac"

VERNAC COMMAND EXTEND Subtac
[ "Program" subtac_gallina_loc(g) ] -> [ Subtac.subtac g ]
  END

let try_catch_exn f e =
  try f e
  with exn -> errorlabstrm "Program" (Cerrors.explain_exn exn)

let subtac_obligation e = try_catch_exn Subtac_obligations.subtac_obligation e
let next_obligation e = try_catch_exn Subtac_obligations.next_obligation e
let try_solve_obligation e = try_catch_exn Subtac_obligations.try_solve_obligation e
let try_solve_obligations e = try_catch_exn Subtac_obligations.try_solve_obligations e
let solve_all_obligations e = try_catch_exn Subtac_obligations.solve_all_obligations e
let admit_obligations e = try_catch_exn Subtac_obligations.admit_obligations e

VERNAC COMMAND EXTEND Subtac_Obligations
| [ "Obligation" integer(num) "of" ident(name) ":" lconstr(t) subtac_withtac(tac) ] -> 
    [ subtac_obligation (num, Some name, Some t) tac ]
| [ "Obligation" integer(num) "of" ident(name) subtac_withtac(tac) ] -> 
    [ subtac_obligation (num, Some name, None) tac ]
| [ "Obligation" integer(num) ":" lconstr(t) subtac_withtac(tac) ] -> 
    [ subtac_obligation (num, None, Some t) tac ]
| [ "Obligation" integer(num) subtac_withtac(tac) ] -> 
    [ subtac_obligation (num, None, None) tac ]
| [ "Next" "Obligation" "of" ident(name) subtac_withtac(tac) ] -> 
    [ next_obligation (Some name) tac ]
| [ "Next" "Obligation" subtac_withtac(tac) ] -> [ next_obligation None tac ]
END

VERNAC COMMAND EXTEND Subtac_Solve_Obligation
| [ "Solve" "Obligation" integer(num) "of" ident(name) "using" tactic(t) ] ->
    [ try_solve_obligation num (Some name) (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligation" integer(num) "using" tactic(t) ] ->
    [ try_solve_obligation num None (Some (Tacinterp.interp t)) ]
      END

VERNAC COMMAND EXTEND Subtac_Solve_Obligations
| [ "Solve" "Obligations" "of" ident(name) "using" tactic(t) ] ->
    [ try_solve_obligations (Some name) (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligations" "using" tactic(t) ] ->
    [ try_solve_obligations None (Some (Tacinterp.interp t)) ]
| [ "Solve" "Obligations" ] ->
    [ try_solve_obligations None None ]
      END

VERNAC COMMAND EXTEND Subtac_Solve_All_Obligations
| [ "Solve" "All" "Obligations" "using" tactic(t) ] ->
    [ solve_all_obligations (Some (Tacinterp.interp t)) ]
| [ "Solve" "All" "Obligations" ] ->
    [ solve_all_obligations None ]
      END

VERNAC COMMAND EXTEND Subtac_Admit_Obligations
| [ "Admit" "Obligations" "of" ident(name) ] -> [ admit_obligations (Some name) ]
| [ "Admit" "Obligations" ] -> [ admit_obligations None ]
    END

VERNAC COMMAND EXTEND Subtac_Set_Solver
| [ "Obligation" "Tactic" ":=" tactic(t) ] -> [
    Subtac_obligations.set_default_tactic 
      (Vernacexpr.use_section_locality ())
      (Tacinterp.glob_tactic t) ]
END

open Pp

VERNAC COMMAND EXTEND Subtac_Show_Solver
| [ "Show" "Obligation" "Tactic" ] -> [
    msgnl (str"Program obligation tactic is " ++ Subtac_obligations.print_default_tactic ()) ]
END

VERNAC COMMAND EXTEND Subtac_Show_Obligations
| [ "Obligations" "of" ident(name) ] -> [ Subtac_obligations.show_obligations (Some name) ]
| [ "Obligations" ] -> [ Subtac_obligations.show_obligations None ]
END

VERNAC COMMAND EXTEND Subtac_Show_Preterm
| [ "Preterm" "of" ident(name) ] -> [ Subtac_obligations.show_term (Some name) ]
| [ "Preterm" ] -> [ Subtac_obligations.show_term None ]
END
