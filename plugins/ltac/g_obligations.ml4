(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
  Syntax for the subtac terms and types.
  Elaborated from correctness/psyntax.ml4 by Jean-Christophe Filliâtre *)

open Constrexpr
open Constrexpr_ops
open Stdarg
open Tacarg
open Extraargs

let (set_default_tactic, get_default_tactic, print_default_tactic) = 
  Tactic_option.declare_tactic_option "Program tactic"

let () =
  (** Delay to recover the tactic imperatively *)
  let tac = Proofview.tclBIND (Proofview.tclUNIT ()) begin fun () ->
    snd (get_default_tactic ())
  end in
  Obligations.default_tactic := tac

let with_tac f tac =
  let env = Genintern.empty_glob_sign (Global.env ()) in
  let tac = match tac with
  | None -> None
  | Some tac ->
    let tac = Genarg.in_gen (Genarg.rawwit wit_ltac) tac in
    let _, tac = Genintern.generic_intern env tac in
    Some tac
  in
  f tac

(* We define new entries for programs, with the use of this module
 * Subtac. These entries are named Subtac.<foo>
 *)

module Gram = Pcoq.Gram
module Tactic = Pltac

open Pcoq

let sigref loc = mkRefC (Libnames.qualid_of_string ~loc "Coq.Init.Specif.sig")

type 'a withtac_argtype = (Tacexpr.raw_tactic_expr option, 'a) Genarg.abstract_argument_type

let wit_withtac : Tacexpr.raw_tactic_expr option Genarg.uniform_genarg_type =
  Genarg.create_arg "withtac"

let withtac = Pcoq.create_generic_entry Pcoq.utactic "withtac" (Genarg.rawwit wit_withtac)

GEXTEND Gram
  GLOBAL: withtac;

  withtac:
    [ [ "with"; t = Tactic.tactic -> Some t
      | -> None ] ]
  ;

  Constr.closed_binder:
    [[ "("; id=Prim.name; ":"; t=Constr.lconstr; "|"; c=Constr.lconstr; ")" ->
          let typ = mkAppC (sigref !@loc, [mkLambdaC ([id], default_binder_kind, t, c)]) in
          [CLocalAssum ([id], default_binder_kind, typ)]
    ] ];

  END

open Obligations

let obligation obl tac = with_tac (fun t -> Obligations.obligation obl t) tac
let next_obligation obl tac = with_tac (fun t -> Obligations.next_obligation obl t) tac

let classify_obbl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND Obligations CLASSIFIED BY classify_obbl
| [ "Obligation" integer(num) "of" ident(name) ":" lglob(t) withtac(tac) ] ->
    [ obligation (num, Some name, Some t) tac ]
| [ "Obligation" integer(num) "of" ident(name) withtac(tac) ] ->
    [ obligation (num, Some name, None) tac ]
| [ "Obligation" integer(num) ":" lglob(t) withtac(tac) ] ->
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

VERNAC COMMAND FUNCTIONAL EXTEND Set_Solver CLASSIFIED AS SIDEFF
| [ "Obligation" "Tactic" ":=" tactic(t) ] -> [
    fun ~atts ~st -> begin
        let open Vernacinterp in
        set_default_tactic
          (Locality.make_section_locality atts.locality)
          (Tacintern.glob_tactic t);
        st
      end]
END

open Pp

VERNAC COMMAND EXTEND Show_Solver CLASSIFIED AS QUERY
| [ "Show" "Obligation" "Tactic" ] -> [
    Feedback.msg_info (str"Program obligation tactic is " ++ print_default_tactic ()) ]
END

VERNAC COMMAND EXTEND Show_Obligations CLASSIFIED AS QUERY
| [ "Obligations" "of" ident(name) ] -> [ show_obligations (Some name) ]
| [ "Obligations" ] -> [ show_obligations None ]
END

VERNAC COMMAND EXTEND Show_Preterm CLASSIFIED AS QUERY
| [ "Preterm" "of" ident(name) ] -> [ Feedback.msg_info (show_term (Some name)) ]
| [ "Preterm" ] -> [ Feedback.msg_info (show_term None) ]
END

open Pp

(* Declare a printer for the content of Program tactics *)
let () =
  let printer _ _ _ = function
  | None -> mt ()
  | Some tac -> str "with" ++ spc () ++ Pptactic.pr_raw_tactic tac
  in
  Pptactic.declare_extra_vernac_genarg_pprule wit_withtac printer
