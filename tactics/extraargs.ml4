(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Pcoq
open Genarg

(* Rewriting orientation *)

let wit_orient, rawwit_orient = Genarg.create_arg "orient"
let orient = Pcoq.create_generic_entry "orient" rawwit_orient
let _ = Tacinterp.add_genarg_interp "orient"
  (fun ist x ->
    (in_gen wit_orient
      (out_gen wit_bool
	(Tacinterp.genarg_interp ist
	  (in_gen wit_bool
	    (out_gen rawwit_orient x))))))

let _ = Metasyntax.add_token_obj "<-"
let _ = Metasyntax.add_token_obj "->"

GEXTEND Gram
  GLOBAL: orient;
  orient:
  [ [ "->" -> true
    | "<-" -> false
    | -> true ] ];
END

let pr_orient = function true -> Pp.str " ->" | false -> Pp.str " <-"

let _ = 
  Pptactic.declare_extra_genarg_pprule
    (rawwit_orient, pr_orient)
    (wit_orient, pr_orient)

 
(* with_constr *)

let wit_with_constr, rawwit_with_constr = Genarg.create_arg "with_constr"
let with_constr = Pcoq.create_generic_entry "with_constr" rawwit_with_constr
let _ = Tacinterp.add_genarg_interp "with_constr"
  (fun ist x ->
    (in_gen wit_with_constr
      (out_gen (wit_opt wit_constr)
	(Tacinterp.genarg_interp ist
	  (in_gen (wit_opt rawwit_constr)
	    (out_gen rawwit_with_constr x))))))

GEXTEND Gram
  GLOBAL: with_constr;
  with_constr:
  [ [ "with"; c = Constr.constr -> Some c
    | -> None ] ];
END

let pr_with_constr prc = function 
  | None -> Pp.mt ()
  | Some c -> Pp.str " with" ++ prc c

let _ = 
  Pptactic.declare_extra_genarg_pprule
    (rawwit_with_constr, pr_with_constr Ppconstr.pr_constr)
    (wit_with_constr, pr_with_constr Printer.prterm)

(*
(* Clause *)
let wit_clause, rawwit_clause = Genarg.create_arg "clause"
let clause = Pcoq.create_generic_entry "clause" rawwit_clause
let _ = Tacinterp.add_genarg_interp "clause"
  (fun ist x ->
    (in_gen wit_clause
      (out_gen (wit_opt wit_constr)
	(Tacinterp.genarg_interp ist
	  (in_gen (wit_opt rawwit_constr)
	    (out_gen rawwit_clause x))))))
*)
