
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

Register int : Set as int31_type.

Delimit Scope int31_scope with int31.
Bind Scope int31_scope with int.

(* Logical operations *)
Register lsl  : int -> int -> int as int31_lsl.
Infix "<<" := lsl (at level 30, no associativity) : int31_scope.

Register lsr  : int -> int -> int as int31_lsr.
Infix ">>" := lsr (at level 30, no associativity) : int31_scope.

Register land : int -> int -> int as int31_land.
Infix "land" := land (at level 40, left associativity) : int31_scope.

Register lor  : int -> int -> int as int31_lor.
Infix "lor" := lor (at level 40, left associativity) : int31_scope.

Register lxor : int -> int -> int as int31_lxor.
Infix "lxor" := lxor (at level 40, left associativity) : int31_scope.

(* Arithmetic modulo operations *)
Register add : int -> int -> int as int31_add.
Notation "n + m" := (add n m) : int31_scope.

Register sub : int -> int -> int as int31_sub.
Notation "n - m" := (sub n m) : int31_scope.

Register mul : int -> int -> int as int31_mul.
Notation "n * m" := (mul n m) : int31_scope.

Register mulc : int -> int -> int * int as int31_mulc.

Register div : int -> int -> int as int31_div.
Notation "n / m" := (div n m) : int31_scope.

Register mod : int -> int -> int as int31_mod.
Notation "n '\%' m" := (mod n m) (at level 40, left associativity) : int31_scope.

(* Comparisons *)
Register eqb : int -> int -> bool as int31_eq.
Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int31_scope.

Register ltb : int -> int -> bool as int31_lt.
Notation "m < n" := (ltb m n) : int31_scope.

Register leb : int -> int -> bool as int31_le.
Notation "m <= n" := (leb m n) : int31_scope.

(* Iterators *)
Register foldi_cont : 
   forall 
     {A B     : Type}
     (f       : int -> (A -> B) -> (A -> B)) 
     (from to : int)
     (cont    : A -> B), 
     A -> B 
     as int31_foldi.

Register foldi_down_cont : 
  forall 
    {A B         : Type}
    (f           :int -> (A -> B) -> (A -> B))
    (from downto : int)
    (cont        : A -> B),
    A -> B 
    as int31_foldi_down.

(* Print *)

Register print_int : int -> int as int31_print.



