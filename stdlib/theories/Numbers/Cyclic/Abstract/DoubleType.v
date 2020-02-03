(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Set Implicit Arguments.

Require Import BinInt.
Local Open Scope Z_scope.

Definition base digits := Z.pow 2 (Zpos digits).
Arguments base digits: simpl never.

#[universes(template)]
Variant carry (A : Type) :=
| C0 : A -> carry A
| C1 : A -> carry A.

Definition interp_carry {A} (sign:Z)(B:Z)(interp:A -> Z) c :=
  match c with
  | C0 x => interp x
  | C1 x => sign*B + interp x
  end.

(** From a type [znz] representing a cyclic structure Z/nZ,
    we produce a representation of Z/2nZ by pairs of elements of [znz]
    (plus a special case for zero). High half of the new number comes
    first.
 *)
#[universes(template)]
Variant zn2z {znz : Type} :=
| W0 : zn2z
| WW : znz -> znz -> zn2z.
Arguments zn2z : clear implicits.

Definition zn2z_to_Z znz (wB:Z) (w_to_Z:znz->Z) (x:zn2z znz) :=
  match x with
  | W0 => 0
  | WW xh xl => w_to_Z xh * wB + w_to_Z xl
  end.

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
