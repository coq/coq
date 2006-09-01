(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*
  Syntax for the subtac terms and types.
  Elaborated from correctness/psyntax.ml4 by Jean-Christophe Filliâtre *)

(* $Id$ *)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Options
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

module SubtacGram =
struct
  let gec s = Gram.Entry.create ("Subtac."^s)
		(* types *)
  let subtac_gallina_loc : Vernacexpr.vernac_expr located Gram.Entry.e = gec "subtac_gallina_loc"
end

open SubtacGram 
open Util

GEXTEND Gram
  GLOBAL: subtac_gallina_loc;
 
  subtac_gallina_loc:
    [ [ g = Vernac.gallina -> loc, g ] ]
    ;
       
  END

type ('a,'b) gallina_loc_argtype = (Vernacexpr.vernac_expr located, 'a, 'b) Genarg.abstract_argument_type

let (wit_subtac_gallina_loc : (Genarg.tlevel, Proof_type.tactic) gallina_loc_argtype),
  (globwit_subtac_gallina_loc : (Genarg.glevel, Tacexpr.glob_tactic_expr) gallina_loc_argtype),
  (rawwit_subtac_gallina_loc : (Genarg.rlevel, Tacexpr.raw_tactic_expr) gallina_loc_argtype) =
  Genarg.create_arg "subtac_gallina_loc"

VERNAC COMMAND EXTEND Subtac
[ "Program" subtac_gallina_loc(g) ] -> [ Subtac.subtac g ]
| [ "Obligation" integer(num) "of" ident(name) ] -> [ Subtac_obligations.subtac_obligation (num, Some name) ]
| [ "Obligation" integer(num) ] -> [ Subtac_obligations.subtac_obligation (num, None) ]      
END
