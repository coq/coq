(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pcoq
open Constr

GEXTEND Gram
  GLOBAL: constr1 pattern;

  pattern:
    [ [ qid = global -> qid
      | "("; p = compound_pattern; ")" -> p ] ]
  ;
  compound_pattern:
    [ [ p = pattern ; lp = ne_pattern_list ->
	  <:ast< (PATTCONSTRUCT $p ($LIST $lp)) >>
      | p = pattern; "as"; id = ident ->
	  <:ast< (PATTAS $id $p)>>
      | p1 = pattern; ","; p2 = pattern ->
          <:ast< (PATTCONSTRUCT  Coq.Init.Datatypes.pair $p1 $p2) >>
      | p = pattern -> p ] ]
  ;
  ne_pattern_list:
    [ [ c1 = pattern; cl = ne_pattern_list -> c1 :: cl
      | c1 = pattern -> [c1] ] ]
  ;
  equation:
    [ [ lhs = ne_pattern_list; "=>"; rhs = constr9 ->
	      <:ast< (EQN $rhs ($LIST $lhs)) >> ] ]
  ;
  ne_eqn_list:
    [ [ e = equation; "|"; leqn = ne_eqn_list -> e :: leqn
      | e = equation -> [e] ] ]
  ;

  constr1:
    [ [ "<"; l1 = lconstr; ">"; "Cases"; lc = ne_constr_list; "of";
        OPT "|"; eqs = ne_eqn_list; "end" ->
          <:ast< (CASES $l1 (TOMATCH ($LIST $lc)) ($LIST $eqs)) >>
      | "Cases"; lc = ne_constr_list; "of";
	OPT "|"; eqs = ne_eqn_list; "end" ->
          <:ast< (CASES "SYNTH" (TOMATCH ($LIST $lc)) ($LIST $eqs)) >>
      | "<"; l1 = lconstr; ">"; "Cases"; lc = ne_constr_list; "of";
        "end" ->
          <:ast< (CASES $l1 (TOMATCH ($LIST $lc))) >>
      | "Cases"; lc = ne_constr_list; "of"; "end" -> 
          <:ast< (CASES "SYNTH" (TOMATCH ($LIST $lc))) >> ] ]
  ;
END;
