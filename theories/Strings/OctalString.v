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
      else if ascii_dec ch "2" then Some 2
      else if ascii_dec ch "3" then Some 3
      else if ascii_dec ch "4" then Some 4
      else if ascii_dec ch "5" then Some 5
      else if ascii_dec ch "6" then Some 6
      else if ascii_dec ch "7" then Some 7
      else None)%N.

Fixpoint pos_oct_app (p q:positive) : positive :=
  match q with
  | 1 => p~0~0~1
  | 2 => p~0~1~0
  | 3 => p~0~1~1
  | 4 => p~1~0~0
  | 5 => p~1~0~1
  | 6 => p~1~1~0
  | 7 => p~1~1~1
  | q~0~0~0 => (pos_oct_app p q)~0~0~0
  | q~0~0~1 => (pos_oct_app p q)~0~0~1
  | q~0~1~0 => (pos_oct_app p q)~0~1~0
  | q~0~1~1 => (pos_oct_app p q)~0~1~1
  | q~1~0~0 => (pos_oct_app p q)~1~0~0
  | q~1~0~1 => (pos_oct_app p q)~1~0~1
  | q~1~1~0 => (pos_oct_app p q)~1~1~0
  | q~1~1~1 => (pos_oct_app p q)~1~1~1
  end.

Module Raw.
  Fixpoint of_pos (p : positive) (rest : string) : string
    := match p with
       | 1 => String "1" rest
       | 2 => String "2" rest
       | 3 => String "3" rest
       | 4 => String "4" rest
       | 5 => String "5" rest
       | 6 => String "6" rest
       | 7 => String "7" rest
       | p'~0~0~0 => of_pos p' (String "0" rest)
       | p'~0~0~1 => of_pos p' (String "1" rest)
       | p'~0~1~0 => of_pos p' (String "2" rest)
       | p'~0~1~1 => of_pos p' (String "3" rest)
       | p'~1~0~0 => of_pos p' (String "4" rest)
       | p'~1~0~1 => of_pos p' (String "5" rest)
       | p'~1~1~0 => of_pos p' (String "6" rest)
       | p'~1~1~1 => of_pos p' (String "7" rest)
       end.

  Fixpoint to_N (s : string) (rest : N)
    : N
    := match s with
       | "" => rest
       | String ch s'
         => to_N
              s'
              match ascii_to_digit ch with
              | Some v => N.add v (N.mul 8 rest)
              | None => N0
              end
       end.

  Fixpoint to_N_of_pos (p : positive) (rest : string) (base : N)
    : to_N (of_pos p rest) base
      = to_N rest match base with
                  | N0 => N.pos p
                  | Npos v => Npos (pos_oct_app v p)
                  end.
  Proof.
    do 3 try destruct p as [p|p|]; destruct base; try reflexivity;
      cbn; rewrite to_N_of_pos; reflexivity.
  Qed.
End Raw.

Definition of_pos (p : positive) : string
  := String "0" (String "o" (Raw.of_pos p "")).
Definition of_N (n : N) : string
  := match n with
     | N0 => "0o0"
     | Npos p => of_pos p
     end.
Definition of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (of_pos p)
     | Z0 => "0o0"
     | Zpos p => of_pos p
     end.
Definition of_nat (n : nat) : string
  := of_N (N.of_nat n).

Definition to_N (s : string) : N
  := match s with
     | String s0 (String so s)
       => if ascii_dec s0 "0"
          then if ascii_dec so "o"
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

Lemma to_Z_of_Z (z : Z)
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

Example of_pos_1 : of_pos 1 = "0o1" := eq_refl.
Example of_pos_2 : of_pos 2 = "0o2" := eq_refl.
Example of_pos_3 : of_pos 3 = "0o3" := eq_refl.
Example of_pos_7 : of_pos 7 = "0o7" := eq_refl.
Example of_pos_8 : of_pos 8 = "0o10" := eq_refl.
Example of_N_0 : of_N 0 = "0o0" := eq_refl.
Example of_Z_0 : of_Z 0 = "0o0" := eq_refl.
Example of_Z_m1 : of_Z (-1) = "-0o1" := eq_refl.
Example of_nat_0 : of_nat 0 = "0o0" := eq_refl.
