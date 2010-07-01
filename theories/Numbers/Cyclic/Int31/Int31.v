
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Export DoubleType.

RegisterInd bool as ind_bool.
RegisterInd prod as ind_pair. 
RegisterInd carry as ind_carry.
RegisterInd comparison as ind_cmp.

Definition size := 31%nat.

Register int31 : Set as int31_type.

Delimit Scope int31_scope with int31.
Bind Scope int31_scope with int31.

(* Logical operations *)
Register lsl31  : int31 -> int31 -> int31 as int31_lsl.
Infix "<<" := lsl31 (at level 30, no associativity) : int31_scope.

Register lsr31  : int31 -> int31 -> int31 as int31_lsr.
Infix ">>" := lsr31 (at level 30, no associativity) : int31_scope.

Register land31 : int31 -> int31 -> int31 as int31_land.
Infix "land" := land31 (at level 40, left associativity) : int31_scope.

Register lor31  : int31 -> int31 -> int31 as int31_lor.
Infix "lor" := lor31 (at level 40, left associativity) : int31_scope.

Register lxor31 : int31 -> int31 -> int31 as int31_lxor.
Infix "lxor" := lor31 (at level 40, left associativity) : int31_scope.

(* Arithmetic modulo operations *)
Register add31 : int31 -> int31 -> int31 as int31_add.
Notation "n + m" := (add31 n m) : int31_scope.

Register sub31 : int31 -> int31 -> int31 as int31_sub.
Notation "n - m" := (sub31 n m) : int31_scope.

Register mul31 : int31 -> int31 -> int31 as int31_mul.
Notation "n * m" := (mul31 n m) : int31_scope.

Register div31 : int31 -> int31 -> int31 as int31_div.
Notation "n / m" := (div31 n m) : int31_scope.

Register mod31 : int31 -> int31 -> int31 as int31_mod.
Notation "n '\%' m" := (mod31 n m) (at level 40, left associativity) : int31_scope.

(* Exact arithmetic operations *)
Register add31c      : int31 -> int31 -> carry int31 as int31_addc.
Notation "n '+c' m" := (add31c n m) (at level 50, no associativity) : int31_scope.

Register add31carryc : int31 -> int31 -> carry int31 as int31_addcarryc.

Register sub31c      : int31 -> int31 -> carry int31 as int31_subc.
Notation "n '-c' m" := (sub31c n m) (at level 50, no associativity) : int31_scope.

Register sub31carryc : int31 -> int31 -> carry int31 as int31_subcarryc.

Register mul31c      : int31 -> int31 -> int31 * int31 as int31_mulc.

Register diveucl31   : int31 -> int31 -> int31 * int31 as int31_diveucl.
Register diveucl31_21    : int31 -> int31 -> int31 -> int31 * int31 as int31_div21.
Register addmuldiv31   : int31 -> int31 -> int31 -> int31 as int31_addmuldiv.

(* Comparisons *)
Register eq31 : int31 -> int31 -> bool as int31_eq.
Notation "m '==' n" := (eq31 m n) (at level 70, no associativity) : bool_scope.

Register lt31 : int31 -> int31 -> bool as int31_lt.
Notation "m < n" := (lt31 m n) : bool_scope.

Register le31 : int31 -> int31 -> bool as int31_le.
Notation "m <= n" := (le31 m n) : bool_scope.

Register compare31 : int31 -> int31 -> comparison as int31_compare.
Notation "n ?= m" := (compare31 n m) (at level 70, no associativity) : int31_scope.
(* Special operations *)
Register head031 : int31 -> int31 as int31_head0.
Register tail031 : int31 -> int31 as int31_tail0.


(* Iterators *)
Register foldi_cont31 : 
   forall 
     (A B     : Type)
     (f       : int31 -> (A -> B) -> (A -> B)) 
     (from to : int31)
     (cont    : A -> B), 
     A -> B 
     as int31_foldi.

Register foldi_down_cont31 : 
  forall 
    (A B         : Type)
    (f           :int31 -> (A -> B) -> (A -> B))
    (from downto : int31)
    (cont        : A -> B),
    A -> B 
    as int31_foldi_down.

(* Print *)

Register print_int : int31 -> int31 as int31_print.