(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ascii String.
Require Import BinNums.
Import BinNatDef.
Import BinIntDef.
Import BinPosDef.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Definition ascii_to_digit (ch : ascii) : option N
  := (if ascii_dec ch "0" then Some 0
      else if ascii_dec ch "1" then Some 1
      else None)%N.

Fixpoint pos_bin_app (p q:positive) : positive :=
  match q with
  | q~0 => (pos_bin_app p q)~0
  | q~1 => (pos_bin_app p q)~1
  | 1 => p~1
  end.

Module Raw.
  Fixpoint of_pos (p : positive) (rest : string) : string
    := match p with
       | 1 => String "1" rest
       | p'~0 => of_pos p' (String "0" rest)
       | p'~1 => of_pos p' (String "1" rest)
       end.

  Fixpoint to_N (s : string) (rest : N)
    : N
    := match s with
       | "" => rest
       | String ch s'
         => to_N
              s'
              match ascii_to_digit ch with
              | Some v => N.add v (N.double rest)
              | None => N0
              end
       end.

  Fixpoint to_N_of_pos (p : positive) (rest : string) (base : N)
    : to_N (of_pos p rest) base
      = to_N rest match base with
                  | N0 => N.pos p
                  | Npos v => Npos (pos_bin_app v p)
                  end.
  Proof.
    destruct p as [p|p|]; destruct base; try reflexivity;
      cbn; rewrite to_N_of_pos; reflexivity.
  Qed.
End Raw.

Definition of_pos (p : positive) : string
  := String "0" (String "b" (Raw.of_pos p "")).
Definition of_N (n : N) : string
  := match n with
     | N0 => "0b0"
     | Npos p => of_pos p
     end.
Definition of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (of_pos p)
     | Z0 => "0b0"
     | Zpos p => of_pos p
     end.
Definition of_nat (n : nat) : string
  := of_N (N.of_nat n).

Definition to_N (s : string) : N
  := match s with
     | String s0 (String sb s)
       => if ascii_dec s0 "0"
          then if ascii_dec sb "b"
               then Raw.to_N s N0
               else N0
          else N0
     | _ => N0
     end.
Definition to_pos (s : string) : positive
  := match to_N s with
     | N0 => 1
     | Npos p => p
     end.
Definition to_Z (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_dec s0 "-"
                              then (true, to_N s')
                              else (false, to_N s)
                         | EmptyString => (false, to_N s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.
Definition to_nat (s : string) : nat
  := N.to_nat (to_N s).

Lemma to_N_of_N (n : N)
  : to_N (of_N n)
    = n.
Proof.
  destruct n; [ reflexivity | apply Raw.to_N_of_pos ].
Qed.

Lemma Z_of_of_Z (z : Z)
  : to_Z (of_Z z)
    = z.
Proof.
  cbv [of_Z to_Z]; destruct z as [|z|z]; cbn;
    try reflexivity;
    rewrite Raw.to_N_of_pos; cbn; reflexivity.
Qed.

Lemma to_nat_of_nat (n : nat)
  : to_nat (of_nat n)
    = n.
Proof.
  cbv [to_nat of_nat];
    rewrite to_N_of_N, Nnat.Nat2N.id; reflexivity.
Qed.

Lemma to_pos_of_pos (p : positive)
  : to_pos (of_pos p)
    = p.
Proof.
  cbv [of_pos to_pos to_N]; cbn;
    rewrite Raw.to_N_of_pos; cbn; reflexivity.
Qed.

Example of_pos_1 : of_pos 1 = "0b1" := eq_refl.
Example of_pos_2 : of_pos 2 = "0b10" := eq_refl.
Example of_pos_3 : of_pos 3 = "0b11" := eq_refl.
Example of_N_0 : of_N 0 = "0b0" := eq_refl.
Example of_Z_0 : of_Z 0 = "0b0" := eq_refl.
Example of_Z_m1 : of_Z (-1) = "-0b1" := eq_refl.
Example of_nat_0 : of_nat 0 = "0b0" := eq_refl.
