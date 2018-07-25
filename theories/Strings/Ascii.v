(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(** Contributed by Laurent Théry (INRIA);
    Adapted to Coq V8 by the Coq Development Team *)

Require Import Bool BinPos BinNat PeanoNat Nnat.
Declare ML Module "ascii_syntax_plugin".

(** * Definition of ascii characters *)

(** Definition of ascii character as a 8 bits constructor *)

Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool).

Delimit Scope char_scope with char.
Bind Scope char_scope with ascii.

Definition zero := Ascii false false false false false false false false.

Definition one := Ascii true false false false false false false false.

Definition shift (c : bool) (a : ascii) :=
  match a with
    | Ascii a1 a2 a3 a4 a5 a6 a7 a8 => Ascii c a1 a2 a3 a4 a5 a6 a7
  end.

(** Definition of a decidable function that is effective *)

Definition ascii_dec : forall a b : ascii, {a = b} + {a <> b}.
Proof.
  decide equality; apply bool_dec.
Defined.

Local Open Scope lazy_bool_scope.

Definition eqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 &&& Bool.eqb a1 b1 &&& Bool.eqb a2 b2 &&& Bool.eqb a3 b3
    &&& Bool.eqb a4 b4 &&& Bool.eqb a5 b5 &&& Bool.eqb a6 b6 &&& Bool.eqb a7 b7
 end.

Infix "=?" := eqb : char_scope.

Lemma eqb_spec (a b : ascii) : reflect (a = b) (a =? b)%char.
Proof.
 destruct a, b; simpl.
 do 8 (case Bool.eqb_spec; [ intros -> | constructor; now intros [= ] ]).
 now constructor.
Qed.

Local Ltac t_eqb :=
  repeat first [ congruence
               | progress subst
               | apply conj
               | match goal with
                 | [ |- context[eqb ?x ?y] ] => destruct (eqb_spec x y)
                 end
               | intro ].
Lemma eqb_refl x : (x =? x)%char = true. Proof. t_eqb. Qed.
Lemma eqb_sym x y : (x =? y)%char = (y =? x)%char. Proof. t_eqb. Qed.
Lemma eqb_eq n m : (n =? m)%char = true <-> n = m. Proof. t_eqb. Qed.
Lemma eqb_neq x y : (x =? y)%char = false <-> x <> y. Proof. t_eqb. Qed.
Lemma eqb_compat: Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) eqb.
Proof. t_eqb. Qed.

(** * Conversion between natural numbers modulo 256 and ascii characters *)

(** Auxiliary function that turns a positive into an ascii by
   looking at the last 8 bits, ie z mod 2^8 *)

Definition ascii_of_pos : positive -> ascii :=
 let loop := fix loop n p :=
   match n with
     | O => zero
     | S n' =>
       match p with
         | xH => one
         | xI p' => shift true (loop n' p')
         | xO p' => shift false (loop n' p')
       end
   end
 in loop 8.

(** Conversion from [N] to [ascii] *)

Definition ascii_of_N (n : N) :=
  match n with
    | N0 => zero
    | Npos p => ascii_of_pos p
  end.

(** Same for [nat] *)

Definition ascii_of_nat (a : nat) := ascii_of_N (N.of_nat a).

(** The opposite functions *)

Local Open Scope list_scope.

Fixpoint N_of_digits (l:list bool) : N :=
 match l with
  | nil => 0
  | b :: l' => (if b then 1 else 0) + 2*(N_of_digits l')
 end%N.

Definition N_of_ascii (a : ascii) : N :=
 let (a0,a1,a2,a3,a4,a5,a6,a7) := a in
 N_of_digits (a0::a1::a2::a3::a4::a5::a6::a7::nil).

Definition nat_of_ascii (a : ascii) : nat := N.to_nat (N_of_ascii a).

(** Proofs that we have indeed opposite function (below 256) *)

Theorem ascii_N_embedding :
  forall a : ascii, ascii_of_N (N_of_ascii a) = a.
Proof.
  destruct a as [[|][|][|][|][|][|][|][|]]; vm_compute; reflexivity.
Qed.

Theorem N_ascii_embedding :
  forall n:N, (n < 256)%N -> N_of_ascii (ascii_of_N n) = n.
Proof.
destruct n.
reflexivity.
do 8 (destruct p; [ | | intros; vm_compute; reflexivity ]);
 intro H; vm_compute in H; destruct p; discriminate.
Qed.

Theorem ascii_nat_embedding :
  forall a : ascii, ascii_of_nat (nat_of_ascii a) = a.
Proof.
  destruct a as [[|][|][|][|][|][|][|][|]]; compute; reflexivity.
Qed.

Theorem nat_ascii_embedding :
  forall n : nat, n < 256 -> nat_of_ascii (ascii_of_nat n) = n.
Proof.
 intros. unfold nat_of_ascii, ascii_of_nat.
 rewrite N_ascii_embedding.
 apply Nat2N.id.
 unfold N.lt.
 change 256%N with (N.of_nat 256).
 rewrite <- Nat2N.inj_compare.
 now apply Nat.compare_lt_iff.
Qed.


(** * Concrete syntax *)

(**
  Ascii characters can be represented in scope char_scope as follows:
  - ["c"]   represents itself if c is a character of code < 128,
  - [""""]  is an exception: it represents the ascii character 34
            (double quote),
  - ["nnn"] represents the ascii character of decimal code nnn.

  For instance, both ["065"] and ["A"] denote the character `uppercase
  A', and both ["034"] and [""""] denote the character `double quote'.

  Notice that the ascii characters of code >= 128 do not denote
  stand-alone utf8 characters so that only the notation "nnn" is
  available for them (unless your terminal is able to represent them,
  which is typically not the case in coqide).
*)

Local Open Scope char_scope.

Example Space := " ".
Example DoubleQuote := """".
Example Beep := "007".
