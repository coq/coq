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

let pr_orient _prc _prt = function
  | true -> Pp.mt ()
  | false -> Pp.str " <-"

ARGUMENT EXTEND orient TYPED AS bool PRINTED BY pr_orient
| [ "->" ] -> [ true ]
| [ "<-" ] -> [ false ]
| [ ] -> [ true ]
END
 
(* with_constr *)

open Tacinterp

let pr_with_constr_gen prc _prtac = function 
  | None -> Pp.mt ()
  | Some c -> Pp.str " with" ++ prc c

ARGUMENT EXTEND with_constr
  TYPED AS constr_opt 
  PRINTED BY pr_with_constr_gen 
  INTERPRETED BY interp_genarg
  GLOBALIZED BY intern_genarg
| [ "with" constr(c) ] -> [ Some c ]
| [ ] -> [ None ]
END
