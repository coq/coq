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

let _ = Metasyntax.add_token_obj "<-"
let _ = Metasyntax.add_token_obj "->"

let pr_orient = function true -> Pp.str " ->" | false -> Pp.str " <-"

ARGUMENT EXTEND orient TYPED AS bool PRINTED BY pr_orient
| [ "->" ] -> [ true ]
| [ "<-" ] -> [ false ]
| [ ] -> [ true ]
END
(*
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
*)
 
(* with_constr *)

open Tacinterp

let pr_with_constr_gen prc = function 
  | None -> Pp.mt ()
  | Some c -> Pp.str " with" ++ prc c

let rawpr_with_constr = pr_with_constr_gen Ppconstr.pr_constr
let pr_with_constr = pr_with_constr_gen Printer.prterm

ARGUMENT EXTEND with_constr
  TYPED AS constr_opt 
  PRINTED BY pr_with_constr 
  INTERPRETED BY genarg_interp
  RAW TYPED AS constr_opt
  RAW PRINTED BY rawpr_with_constr
| [ "with" constr(c) ] -> [ Some c ]
| [ ] -> [ None ]
END

(*
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
*)
