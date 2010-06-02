(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction of [nat] into Ocaml's [int] *)

(** Nota: this is potentially unsafe since [int] is bounded
    while [nat] isn't, so you should make sure that no overflow
    occurs in your programs... *)

Require Import Arith Compare_dec ExtrOcamlBasic.

Extract Inductive sumbool => bool [ true false ].

Extract Inductive nat => int [ "0" "succ" ]
 "(*nat_case*) (fun fO fS n => if n=0 then fO () else fS (n-1))".

Extract Constant plus => "(+)".
Extract Constant pred => "fun n => max 0 (n-1)".
Extract Constant minus => "fun n m => max 0 (n-p)".
Extract Constant mult => "( * )".
Extract Constant nat_compare =>
 "fun n m => if n=m then Eq else if n<m then Lt else Gt".

Extract Constant leb => "(<=)".
Extract Constant nat_beq => "(=)".

Extraction fact.

(* Div2.div2 *)
(* Even.even_odd_dec *)
(* beq_nat ?? eq_nat_dec le_lt_dec, etc *)
