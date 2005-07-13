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

open Sast

(* We define new entries for programs, with the use of this module
 * Subtac. These entries are named Subtac.<foo>
 *)

module Gram = Pcoq.Gram
module Constr = Pcoq.Constr
module Tactic = Pcoq.Tactic

module Subtac =
  struct
    let gec s = Gram.Entry.create ("Subtac."^s)
    (* types *)
    let subtac_spec : type_loc Gram.Entry.e = gec "subtac_spec"
    let subtac_term : term_loc Gram.Entry.e = gec "subtac_term"
    let subtac_wf_proof_type : Scoq.wf_proof_type Gram.Entry.e = gec "subtac_wf_proof_type"

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
open Coqast

if not !Options.v7 then
GEXTEND Gram
  GLOBAL: subtac_spec subtac_term subtac_wf_proof_type;

  (* Types ******************************************************************)
  subtac_spec: 
    [ 
      "10" LEFTA
	[ t = subtac_spec; t' = subtac_spec -> loc, TApp (t, t') ]
    
    | [ t = subtac_spec_no_app -> t ]
    ];

  subtac_spec_no_app: 
    [ [      
	  "(" ; t = subtac_spec_lpar_open -> t
	| "[" ; x = subtac_binder_opt; "]"; t = subtac_spec -> 
	    loc, TSigma (x, t)
	| "{" ; x = subtac_binder; "|"; p = subtac_spec; "}"; "->"; t = subtac_spec ->
	    let ((locx, i), tx) = x in
	      loc, TPi (((locx, Name i), (loc, TSubset (x, p))), t)
	| "{" ; x = subtac_binder; "|"; p = subtac_spec; "}" ->
	    loc, TSubset(x, p)
	| t = subtac_type_ident; f = subtac_spec_tident -> f t
	]
    ]
  ;
  
  subtac_spec_no_app_loc: 
    [ [ x = subtac_spec_no_app -> (loc, x) ] 
  ];

  subtac_spec_tident:
    [ [
	"->"; t' = subtac_spec -> 
	  fun t -> loc, TPi (((dummy_loc, Anonymous), t), t')
      | -> (fun x -> x)
      ]
    ]
  ;

  subtac_spec_lpar_open:
    [
      [ s = subtac_identifier; t = subtac_spec_lpar_name -> t s 
      | s = subtac_spec; ")" -> s ]
    ]
  ;

  subtac_spec_lpar_name:
    [
      [ ":" ; y = subtac_spec; ")"; t = subtac_spec -> 
	  (fun s -> loc, TPi ((((fst s), Name (snd s)), y), t))
      | l = LIST1 subtac_spec_no_app_loc; ")" -> fun s -> 
	  List.fold_left (fun acc x -> 
			    (join_loc (fst acc) (fst x), TApp (acc, snd x)))
	    (fst s, TIdent s) l
      ]
    ]
  ;

  subtac_binder:
    [ [ s = subtac_identifier; ":"; t = subtac_spec -> let (l,s) = s in
	  ((loc, s), t) 
    | "{"; x = subtac_binder; "|"; p = subtac_spec; "}" -> 
	let ((l, s), t) = x in 
	  ((l, s), (loc, TSubset (x, p)))
      ]
    ]
  ;

  subtac_identifier:
    [ [ s = IDENT -> (loc, id_of_string s) ] ]
  ;

  subtac_real_name:
    [ [ s = IDENT -> (loc, Name (id_of_string s))
      (* | "_" -> loc, Anonymous111 *)
      ] ]
  ;
  
  subtac_name:
    [ [ n = OPT subtac_real_name -> match n with Some n -> n | None -> loc, Anonymous ] ]
  ;
  
  subtac_binder_opt:
    [ [ s = subtac_name; ":"; t = subtac_spec -> (s, t) ] ]
  ;
  
  subtac_type_ident:
    [ [ s = subtac_identifier -> loc, TIdent s ] ]
  ;

  subtac_term:
    [ 
      "20" LEFTA
	[ t = subtac_term; t' = subtac_term -> 
	    let loc = join_loc (fst t) (fst t') in
	      loc, SApp (t, t')
	]
    | "10"
    	[ 
	  i = subtac_identifier -> loc, SIdent i
	| "fun"; bl = LIST1 subtac_binder; "=>"; p = subtac_term ->
	    (List.fold_left 
	       (fun acc (((loc, s), (loc', t)) as b) -> 
		  (join_loc loc (fst acc), SLambda (b, acc))) p bl)
	| "let"; "("; nl = LIST0 subtac_name SEP ","; ")" ; "="; t = subtac_term;
	  "in"; t' = subtac_term ->
	    loc, (SLetTuple (nl, t, t'))
	| "let"; i = subtac_name; "="; t = subtac_term; "in"; t' = subtac_term ->
	    loc, (SLetIn (i, t, t'))
	| "if"; b = subtac_term; "then"; t = subtac_term; "else"; t' = subtac_term ->
	    loc, SIfThenElse (b, t, t')
	| "("; t = subtac_lpar_term -> t
	]
	
    ]
  ;

  subtac_lpar_term:
    [ [
	x = test_id_coloneq; t = subtac_term; ","; 
	t' = subtac_term; ":"; tt = subtac_spec; ")" ->
	  (loc, (SSumDep (((dummy_loc, x), t), (t', tt))))
      | t = subtac_term; f = subtac_lpar_term_term -> f t
      ]
    ]
  ;

  subtac_lpar_term_term:
    [ [
	","; t' = subtac_term; ")" ->
	  (fun t -> loc, (SSumInf (t, t')))
      | ")" -> (fun x -> x)
      ] ]
  ;

  subtac_wf_proof_type:
    [ [ IDENT "proof"; t = Constr.constr -> 
	  Scoq.ManualProof (Scoq.constr_of t)
      | IDENT "auto" -> Scoq.AutoProof
      | -> Scoq.ExistentialProof
      ]
    ]
  ;
  END
else (* Developped with Coq 8.0 *) ()

type type_loc_argtype = (type_loc, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type
type term_loc_argtype = (term_loc, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type
type wf_proof_type_argtype = (Scoq.wf_proof_type, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type

let (wit_subtac_spec : type_loc_argtype),
  (globwit_subtac_spec : type_loc_argtype),
  (rawwit_subtac_spec  : type_loc_argtype) =
  Genarg.create_arg "subtac_spec"

let (wit_subtac_term : term_loc_argtype),
  (globwit_subtac_term : term_loc_argtype),
  (rawwit_subtac_term  : term_loc_argtype) =
  Genarg.create_arg "subtac_term"

let (wit_subtac_wf_proof_type : wf_proof_type_argtype),
  (globwit_subtac_wf_proof_type : wf_proof_type_argtype),
  (rawwit_subtac_wf_proof_type : wf_proof_type_argtype) =
  Genarg.create_arg "subtac_wf_proof_type"

VERNAC COMMAND EXTEND SubtacRec
[ "Recursive" "program" ident(id) 
  "(" ident(recid) ":" subtac_spec(rect) ")" 
  "using" constr(wf_relation)
  subtac_wf_proof_type(wf)
  ":" subtac_spec(s) ":=" subtac_term(t) ] -> 
  [ Rewrite.subtac (Some (recid, rect, 
			  Scoq.constr_of wf_relation, wf)) id (s, t) ]
END
  
VERNAC COMMAND EXTEND Subtac
[ "Program" ident(id) ":" subtac_spec(s) ":=" subtac_term(t) ] -> 
[ Rewrite.subtac None id (s, t) ]
END
