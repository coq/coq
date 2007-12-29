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

(* $Id$ *)


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

  let subtac_nameopt : identifier option Gram.Entry.e = gec "subtac_nameopt"
end

open SubtacGram 
open Util
open Pcoq

let sigref = mkRefC (Qualid (dummy_loc, Libnames.qualid_of_string "Coq.Init.Specif.sig"))

GEXTEND Gram
  GLOBAL: subtac_gallina_loc Constr.binder_let Constr.binder subtac_nameopt;
 
  subtac_gallina_loc:
    [ [ g = Vernac.gallina -> loc, g
    | g = Vernac.gallina_ext -> loc, g ] ]
    ;

  subtac_nameopt:
    [ [ "ofb"; id=Prim.ident -> Some (id) 
      | -> None ] ]
    ;

  Constr.binder_let:
    [ [ "("; id=Prim.name; ":"; t=Constr.lconstr; "|"; c=Constr.lconstr; ")" -> 
	  let typ = mkAppC (sigref, [mkLambdaC ([id], default_binder_kind, t, c)]) in
	    LocalRawAssum ([id], default_binder_kind, typ)
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

type 'a nameopt_argtype = (identifier option, 'a) Genarg.abstract_argument_type

let (wit_subtac_nameopt : Genarg.tlevel nameopt_argtype),
  (globwit_subtac_nameopt : Genarg.glevel nameopt_argtype),
  (rawwit_subtac_nameopt : Genarg.rlevel nameopt_argtype) =
  Genarg.create_arg "subtac_nameopt"

VERNAC COMMAND EXTEND Subtac
[ "Program" subtac_gallina_loc(g) ] -> [ Subtac.subtac g ]
  END

VERNAC COMMAND EXTEND Subtac_Obligations
| [ "Obligation" integer(num) "of" ident(name) ":" lconstr(t) ] -> [ Subtac_obligations.subtac_obligation (num, Some name, Some t) ]
| [ "Obligation" integer(num) "of" ident(name) ] -> [ Subtac_obligations.subtac_obligation (num, Some name, None) ]
| [ "Obligation" integer(num) ":" lconstr(t) ] -> [ Subtac_obligations.subtac_obligation (num, None, Some t) ]      
| [ "Obligation" integer(num) ] -> [ Subtac_obligations.subtac_obligation (num, None, None) ]
| [ "Next" "Obligation" "of" ident(name) ] -> [ Subtac_obligations.next_obligation (Some name) ]
| [ "Next" "Obligation" ] -> [ Subtac_obligations.next_obligation None ]
END

VERNAC COMMAND EXTEND Subtac_Solve_Obligation
| [ "Solve" "Obligation" integer(num) "of" ident(name) "using" tactic(t) ] -> 
    [ Subtac_obligations.try_solve_obligation num (Some name) (Tacinterp.interp t) ]
| [ "Solve" "Obligation" integer(num) "using" tactic(t) ] -> 
    [ Subtac_obligations.try_solve_obligation num None (Tacinterp.interp t) ]
      END

VERNAC COMMAND EXTEND Subtac_Solve_Obligations
| [ "Solve" "Obligations" "of" ident(name) "using" tactic(t) ] -> 
    [ Subtac_obligations.try_solve_obligations (Some name) (Tacinterp.interp t) ]
| [ "Solve" "Obligations" "using" tactic(t) ] -> 
    [ Subtac_obligations.try_solve_obligations None (Tacinterp.interp t) ]
| [ "Solve" "Obligations" ] -> 
    [ Subtac_obligations.try_solve_obligations None (Subtac_obligations.default_tactic ()) ]
      END

VERNAC COMMAND EXTEND Subtac_Solve_All_Obligations
| [ "Solve" "All" "Obligations" "using" tactic(t) ] -> 
    [ Subtac_obligations.solve_all_obligations (Tacinterp.interp t) ]
| [ "Solve" "All" "Obligations" ] -> 
    [ Subtac_obligations.solve_all_obligations (Subtac_obligations.default_tactic ()) ]
      END

VERNAC COMMAND EXTEND Subtac_Admit_Obligations
| [ "Admit" "Obligations" "of" ident(name) ] -> [ Subtac_obligations.admit_obligations (Some name) ] 
| [ "Admit" "Obligations" ] -> [ Subtac_obligations.admit_obligations None ] 
    END

VERNAC COMMAND EXTEND Subtac_Set_Solver
| [ "Obligations" "Tactic" ":=" tactic(t) ] -> [ Subtac_obligations.set_default_tactic (Tacinterp.glob_tactic t) ]
END

VERNAC COMMAND EXTEND Subtac_Show_Obligations
| [ "Obligations" "of" ident(name) ] -> [ Subtac_obligations.show_obligations (Some name) ]
| [ "Obligations" ] -> [ Subtac_obligations.show_obligations None ]
END
