(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i $Id: i*)
Require Export Axioms.
Require Export LtProps.

(*s Axiomatizing [>=] from [<] *)

Axiom not_lt_ge : (x,y:N)~(x<y)->(x>=y).
Axiom ge_not_lt : (x,y:N)(x>=y)->~(x<y).

Hints Resolve not_lt_ge : num.
Hints Immediate ge_not_lt : num.
