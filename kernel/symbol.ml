(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util

(* equational theories *)
type eqth = Free | C | AC

(* statuses *)
type status = Mul | Lex | RevLex | Comb of (int list) list

(* say if a combination is linear *)
let is_linear_comb =
  let indices = ref [] in
  let rec is_linear_mul = function
    | i::m' ->
	if List.mem i !indices then false
	else (indices := i::!indices; is_linear_mul m')
    | _ -> true
  in
  let rec is_linear_lex = function
    | m::l' -> is_linear_mul m & is_linear_lex l'
    | _ -> true
  in
    fun l -> indices := []; is_linear_lex l

(* say if a status is linear *)
let is_linear = function
  | Comb l -> is_linear_comb l
  | _ -> true

(* kinds of occurrences *)
type delta = Pos | Neg | Nul

let opp = function
  | Pos -> Neg
  | Neg -> Pos
  | _ -> Nul

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
}
