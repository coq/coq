(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Quote

TACTIC EXTEND quote
  [ "quote" ident(f) ] -> [ quote f [] ]
| [ "quote" ident(f) "[" ne_ident_list(lc) "]"] -> [ quote f lc ]
END
