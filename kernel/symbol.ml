(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Precedence

(* equational theories *)
type eqth = Free | C | AC

(* statuses *)
type status = Mul | Lex | RLex | Comb of (int list) list

(* combination of elements of [vt] whose indices are given by [l] *)
let select vt =
  (* elements of [vt] whose indices are given by [m] *)
  let rec sel m =
    match m with
      | i::m' -> vt.(i)::(sel m')
      | _ -> []
  in
  let rec selc l =
    match l with
      | m::l' -> (sel m)::(selc l')
      | _ -> []
  in selc

let rec gen_list_mul n = if n <= 0 then [] else n::(gen_list_mul (n-1))
let rec gen_list_rlex n = if n <= 0 then [] else [n]::(gen_list_rlex (n-1))
let rec gen_list_lex n = List.rev (gen_list_rlex n)

let select_from_status vt = function
  | Mul -> select vt [gen_list_mul (Array.length vt)]
  | Lex -> select vt (gen_list_lex (Array.length vt))
  | RLex -> select vt (gen_list_rlex (Array.length vt))
  | Comb l -> select vt l

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
  symb_prec_defs : prec_def list;
}
