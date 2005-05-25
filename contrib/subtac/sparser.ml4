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

    (* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
    (* admissible notation "(x t)" 
       taken from g_constrnew.ml4 *)
    let lpar_id_coloneq =
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

    let id_coloneq =
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
	     
    (*let identifier = gec "identifier"
    let name = gec "name"
      let type_ident = gec "type_ident"
      let term_ident = gec "term_ident"
  (* binders *)
      let binder  = gec "binder"
      let binder_opt = gec "binder_opt"
  (*let binders  = gec "binders"*)
    (* programs *)
    let term = gec "term"
    let arg = gec "arg"
    let name = gec "name"*)
end 

open Subtac
open Util
open Coqast

GEXTEND Gram
  GLOBAL: subtac_spec subtac_term;

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
	| "[" ; x = binder_opt; "]"; t = subtac_spec -> loc, TSigma (x, t)
	| "{" ; x = binder; "|"; p = subtac_spec; "}"; "->"; t = subtac_spec ->
	    let ((locx, i), tx) = x in
	      loc, TPi (((locx, Name i), (loc, TSubset (x, p))), t)
	| "{" ; x = binder; "|"; p = subtac_spec; "}" ->
	    loc, TSubset(x, p)
	| t = type_ident; f = subtac_spec_tident -> f t
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
      [ s = identifier; t = subtac_spec_lpar_name -> t s 
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

  binder:
    [ [ s = identifier; ":"; t = subtac_spec -> let (l,s) = s in
	  ((loc, s), t) 
    | "{"; x = binder; "|"; p = subtac_spec; "}" -> 
	let ((l, s), t) = x in 
	  ((l, s), (loc, TSubset (x, p)))
      ]
    ]
  ;

  identifier:
    [ [ s = IDENT -> (loc, id_of_string s) ] ]
  ;

  name':
    [ [ s = IDENT -> (loc, Name (id_of_string s))
      | "_" -> loc, Anonymous
      ] ]
  ;
  
  name:
    [ [ n = OPT name' -> match n with Some n -> n | None -> loc, Anonymous ] ]
  ;
  
  binder_opt:
    [ [ s = name; ":"; t = subtac_spec -> (s, t) ] ]
  ;
  
  type_ident:
    [ [ s = identifier -> loc, TIdent s ] ]
  ;

(*   term_ident: *)
(*     [ [ s = identifier -> SIdent s ] ] *)
(*   ; *)
  
(*   lpar_colon_id: *)
(*     [ [ i = lpar_id_coloneq -> loc, i ] ] *)
(*   ; *)

  subtac_term:
    [ 
      "20" LEFTA
	[ t = subtac_term; t' = subtac_term -> 
	    let loc = join_loc (fst t) (fst t') in
	      loc, SApp (t, t')
	]
    | "10"
    	[ 
	  i = identifier -> loc, SIdent i
	| "fun"; bl = LIST1 binder; "=>"; p = subtac_term ->
	    (List.fold_left 
	       (fun acc (((loc, s), (loc', t)) as b) -> 
		  (join_loc loc (fst acc), SLambda (b, acc))) p bl)
	| "let"; "("; nl = LIST0 name SEP ","; ")" ; "="; t = subtac_term;
	  "in"; t' = subtac_term ->
	    loc, (SLetTuple (nl, t, t'))
	| "let"; i = name; "="; t = subtac_term; "in"; t' = subtac_term ->
	    loc, (SLetIn (i, t, t'))
	| "if"; b = subtac_term; "then"; t = subtac_term; "else"; t' = subtac_term ->
	    loc, SIfThenElse (b, t, t')
	| "("; t = lpar_term -> t
	]
	
    ]
  ;

  lpar_term:
    [ [
	x = id_coloneq; t = subtac_term; ","; 
	t' = subtac_term; ":"; tt = subtac_spec; ")" ->
	  (loc, (SSumDep (((dummy_loc, x), t), (t', tt))))
      | t = subtac_term; f = lpar_term_term -> f t
      ]
    ]
  ;

  lpar_term_term:
    [ [
	","; t' = subtac_term; ")" ->
	  (fun t -> loc, (SSumInf (t, t')))
      | ")" -> (fun x -> x)
      ] ]
  ;
  (*
  subtac_term_lpar_open_ident:
    [ [ ":="; t = subtac_term; ","; t' = subtac_term; ":"; tt = subtac_spec; ")" ->
	  (fun x -> (loc, (SSumDep ((x, t), (t', tt)))))
      | t = subtac_term; ")" ->
	  (fun x -> loc, SApp ((fst x, (SIdent x)), t))

      ]
    ]
  ;


  sigma_binder:
    [ [ s = OPT subtac_annot_identifier; t = subtac_term; topt = OPT subtac_annot_type ->	  
	  (s, t, topt) ] ]
  ;
 
  subtac_annot_type:
    [ [ ":"; t = subtac_spec -> t ] ]
  ;

  subtac_annot_identifier: 
    [ [ s = identifier; ":=" -> s ] ]
  ;
*)
(*  
  ast1:
    [ [ x = prog2; IDENT "or"; y = prog1  -> bool_or loc x y
      | x = prog2; IDENT "and"; y = prog1 -> bool_and loc x y
      | x = prog2 -> x
      ] ]
  ;
  ast2:
    [ [ IDENT "not"; x = prog3 -> bool_not loc x
      | x = prog3 -> x
      ] ]
  ;
  ast3:
    [ [ x = prog4; rel = relation; y = prog4 -> bin_op rel loc x y
      | x = prog4 -> x
      ] ]
    ;
  ast4:
    [ [ x = prog5; "+"; y = prog4 -> bin_op "Zplus" loc x y
      | x = prog5; "-"; y = prog4 -> bin_op "Zminus" loc x y
      | x = prog5 -> x
      ] ]
    ;
  ast5:
    [ [ x = prog6; "*"; y = prog5 -> bin_op "Zmult" loc x y 
      | x = prog6 -> x
      ] ]
    ;
  ast6:
    [ [ "-"; x = prog6 -> un_op "Zopp" loc x
      | x = ast7 -> without_effect loc x
      ] ]
    ;

  relation:
    [ [ "<"  -> "Z_lt_ge_bool"
      | "<=" -> "Z_le_gt_bool"
      | ">"  -> "Z_gt_le_bool"
      | ">=" -> "Z_ge_lt_bool"
      | "="  -> "Z_eq_bool"
      | "<>" -> "Z_noteq_bool" ] ] 
  ;
*)
  END
;;


type type_loc_argtype = (type_loc, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type
type term_loc_argtype = (term_loc, constr_expr, Tacexpr.raw_tactic_expr) Genarg.abstract_argument_type

let (wit_subtac_spec : type_loc_argtype),
  (globwit_subtac_spec : type_loc_argtype),
  (rawwit_subtac_spec  : type_loc_argtype) =
  Genarg.create_arg "subtac_spec"

let (wit_subtac_term : term_loc_argtype),
  (globwit_subtac_term : term_loc_argtype),
  (rawwit_subtac_term  : term_loc_argtype) =
  Genarg.create_arg "subtac_term"


VERNAC COMMAND EXTEND SubtacRec
    [ "Recursive" "program" ident(id) "(" ident(recid) ":" subtac_spec(rect) ")" ":" subtac_spec(s) ":=" subtac_term(t) ] -> 
      [ Rewrite.subtac (Some (recid, rect)) id (s, t) ]
END

VERNAC COMMAND EXTEND Subtac
  [ "Program" ident(id) ":" subtac_spec(s) ":=" subtac_term(t) ] -> 
    [ Rewrite.subtac None id (s, t) ]
END
