(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Precedence

(* equational theories *)
type eqth = Free | C | AC

(* statuses *)
type status = Mul | Lex | RLex | Comb of (int list) list

(* combination of elements of [vt] whose indices are given by [l] *)
val select : 'a array -> (int list) list -> ('a list) list
val select_from_status : 'a array -> status -> ('a list) list

(* kinds of occurrences *)
type delta = Pos | Neg | Nul

val opp : delta -> delta

(* termination criteria *)
type termin = General_Schema

(* information about symbols *)
type symbol_info = {
  symb_arity : int;
  symb_eqth : eqth;
  symb_status : status;
  symb_mons : delta array;
  symb_termin : termin;
  symb_acc : bool array;
  symb_prec_defs : prec_def list;
}
