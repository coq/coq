
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Open Local Scope Z_scope.

Section Carry.

 Variable A : Set.

 Inductive carry : Set :=
  | C0 : A -> carry
  | C1 : A -> carry.

End Carry.

Section Zn2Z.

 Variable znz : Set.

 Inductive zn2z : Set :=
  | W0 : zn2z
  | WW : znz -> znz -> zn2z.

 Definition zn2z_to_Z (wB:Z) (w_to_Z:znz->Z) (x:zn2z) :=
  match x with
  | W0 => 0
  | WW xh xl => w_to_Z xh * wB + w_to_Z xl
  end.

 Definition base digits := Zpower 2 (Zpos digits).

 Definition interp_carry sign B (interp:znz -> Z) c :=
  match c with
  | C0 x => interp x
  | C1 x => sign*B + interp x
  end.

End Zn2Z.

Implicit Arguments W0 [znz].

Fixpoint word_tr (w:Set) (n:nat) {struct n} : Set :=
 match n with
 | O => w
 | S n => word_tr (zn2z w) n
 end.

Fixpoint word (w:Set) (n:nat) {struct n} : Set :=
 match n with
 | O => w
 | S n => zn2z (word w n)
 end.

