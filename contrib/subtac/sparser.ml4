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
module Constr = Pcoq.Constr
module Tactic = Pcoq.Tactic
module Prim = Pcoq.Prim

module Subtac =
  struct
    let gec s = Gram.Entry.create ("Subtac."^s)
    (* types *)
    let subtac_wf_proof_type : Scoq.wf_proof_type Gram.Entry.e = gec "subtac_wf_proof_type"
    let subtac_binders : Scoq.binders Gram.Entry.e = gec "subtac_binders"
    let subtac_fixannot : Scoq.recursion_order option Gram.Entry.e = gec "subtac_fixannot"

    (* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
    (* admissible notation "(x t)" 
       taken from g_constrnew.ml4 *)
    let test_lpar_id_coloneq =
      Gram.Entry.of_parser "test_lpar_id_coloneq"
	(fun strm ->
	   Pp.msgnl (Pp.str ("Testing lpar_id_coloneq:" ^ 
			       (snd (List.hd (Stream.npeek 1 strm)))));
	   
	   match Stream.npeek 1 strm with
             | [("","(")] ->
		 (match Stream.npeek 2 strm with
		    | [_; ("IDENT",s)] ->
			(match Stream.npeek 3 strm with
			   | [_; _; ("", ":=")] ->
                               Stream.junk strm; Stream.junk strm; Stream.junk strm;
			       Pp.msgnl (Pp.str "Success");
                               Names.id_of_string s
			   | _ -> raise Stream.Failure)
		    | _ -> raise Stream.Failure)
             | _ -> raise Stream.Failure)

    let test_id_coloneq =
      Gram.Entry.of_parser "test_id_coloneq"
	(fun strm ->
	   Pp.msgnl (Pp.str ("Testing id_coloneq:" ^ 
			       (snd (List.hd (Stream.npeek 1 strm)))));
	   
	   (match Stream.npeek 1 strm with
	      | [("IDENT",s)] ->
		  (match Stream.npeek 2 strm with
		     | [_; ("", ":=")] ->
                         Stream.junk strm; Stream.junk strm;
			 Pp.msgnl (Pp.str "Success");
                         Names.id_of_string s
		     | _ -> raise Stream.Failure)
	      | _ -> raise Stream.Failure))
end 

open Subtac
open Util

GEXTEND Gram
  GLOBAL: subtac_wf_proof_type subtac_binders subtac_fixannot;
 
  subtac_wf_proof_type:
    [ [ IDENT "proof"; t = Constr.constr -> 
	  Scoq.ManualProof t
      | IDENT "auto" -> Scoq.AutoProof
      | -> Scoq.ExistentialProof
      ]
    ]
    ;
  
  subtac_fixannot:
    [ [ "{"; IDENT "struct"; id=Prim.name; "}" -> Some (Scoq.StructRec id)
      | "{"; IDENT "wf"; rel= Constr.constr; id=Prim.name; "}" -> Some (Scoq.WfRec (rel, id))
      | -> None ] ]
  ;

  subtac_binders: [ [ bl = LIST0 Constr.binder_let -> bl ] ]
  ;
  END

type wf_proof_type_argtype = (Scoq.wf_proof_type, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type

let (wit_subtac_wf_proof_type : wf_proof_type_argtype),
  (globwit_subtac_wf_proof_type : wf_proof_type_argtype),
  (rawwit_subtac_wf_proof_type : wf_proof_type_argtype) =
  Genarg.create_arg "subtac_wf_proof_type"

type subtac_binders_argtype = (Scoq.binders, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type

let (wit_subtac_binders : subtac_binders_argtype),
  (globwit_subtac_binders : subtac_binders_argtype),
  (rawwit_subtac_binders : subtac_binders_argtype) =
  Genarg.create_arg "subtac_binders"

type subtac_fixannot_argtype = (Scoq.recursion_order option, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type

let (wit_subtac_fixannot : subtac_fixannot_argtype),
  (globwit_subtac_fixannot : subtac_fixannot_argtype),
  (rawwit_subtac_fixannot : subtac_fixannot_argtype) =
  Genarg.create_arg "subtac_fixannot"

VERNAC COMMAND EXTEND SubtacRec
[ "Recursive" "program" ident(id) subtac_binders(l) subtac_fixannot(f)
    ":" lconstr(s) ":=" lconstr(t) ] -> 
  [ Interp.subtac (Some f) id l Environ.empty_env (s, t) ]
END
  
VERNAC COMMAND EXTEND Subtac
[ "Program" ident(id) subtac_binders(l) ":" lconstr(s) ":=" lconstr(t) ] -> 
  [ Interp.subtac None id l Environ.empty_env (s, t) ]
END
