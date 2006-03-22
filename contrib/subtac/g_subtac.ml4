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

(* type wf_proof_type_argtype = (Subtac_utils.wf_proof_type, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type *)

(* let (wit_subtac_wf_proof_type : wf_proof_type_argtype), *)
(*   (globwit_subtac_wf_proof_type : wf_proof_type_argtype), *)
(*   (rawwit_subtac_wf_proof_type : wf_proof_type_argtype) = *)
(*   Genarg.create_arg "subtac_wf_proof_type" *)

type gallina_loc_argtype = (Vernacexpr.vernac_expr located, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type

let (wit_subtac_gallina_loc : gallina_loc_argtype),
  (globwit_subtac_gallina_loc : gallina_loc_argtype),
  (rawwit_subtac_gallina_loc : gallina_loc_argtype) =
  Genarg.create_arg "subtac_gallina_loc"

(* type subtac_recdef_argtype = (Subtac_utils.recursion_order option, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type *)

(* let (wit_subtac_recdef : subtac_recdef_argtype), *)
(*   (globwit_subtac_recdef : subtac_recdef_argtype), *)
(*   (rawwit_subtac_recdef : subtac_recdef_argtype) = *)
(*   Genarg.create_arg "subtac_recdef" *)

(* VERNAC COMMAND EXTEND SubtacRec *)
(* [ "Recursive" "program" ident(id) subtac_binders(l) subtac_recdef(f) ] ->  *)
(*   [ Interp.subtac id l Environ.empty_env f ] *)
(* END *)
  
VERNAC COMMAND EXTEND Subtac
[ "Program" subtac_gallina_loc(g) ] -> 
  [ Subtac.subtac g ]
END
