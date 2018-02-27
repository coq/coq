(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Local Open Scope Z_scope.

Definition base digits := Z.pow 2 (Zpos digits).
Arguments base digits: simpl never.

Section Carry.

 Variable A : Type.

 Inductive carry :=
  | C0 : A -> carry
  | C1 : A -> carry.

 Definition interp_carry (sign:Z)(B:Z)(interp:A -> Z) c :=
  match c with
  | C0 x => interp x
  | C1 x => sign*B + interp x
  end.

End Carry.

Section Zn2Z.

 Variable znz : Type.

 (** From a type [znz] representing a cyclic structure Z/nZ,
     we produce a representation of Z/2nZ by pairs of elements of [znz]
     (plus a special case for zero). High half of the new number comes
     first.
 *)

 Inductive zn2z :=
  | W0 : zn2z
  | WW : znz -> znz -> zn2z.

 Definition zn2z_to_Z (wB:Z) (w_to_Z:znz->Z) (x:zn2z) :=
  match x with
  | W0 => 0
  | WW xh xl => w_to_Z xh * wB + w_to_Z xl
  end.

End Zn2Z.

Arguments W0 {znz}.

(** From a cyclic representation [w], we iterate the [zn2z] construct
    [n] times, gaining the type of binary trees of depth at most [n],
    whose leafs are either W0 (if depth < n) or elements of w
    (if depth = n).
*)

Fixpoint word (w:Type) (n:nat) : Type :=
 match n with
 | O => w
 | S n => zn2z (word w n)
 end.
