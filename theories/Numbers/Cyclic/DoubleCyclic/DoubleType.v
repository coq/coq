(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

Require Import ZArith.
Open Local Scope Z_scope.

Definition base digits := Zpower 2 (Zpos digits).

Section Carry.

 Variable A : Set.

 Inductive carry : Set :=
  | C0 : A -> carry
  | C1 : A -> carry.

 Definition interp_carry (sign:Z)(B:Z)(interp:A -> Z) c :=
  match c with
  | C0 x => interp x
  | C1 x => sign*B + interp x
  end.

End Carry.

Section Zn2Z.

 Variable znz : Set.

 (** From a type [znz] representing a cyclic structure Z/nZ, 
     we produce a representation of Z/2nZ by pairs of elements of [znz]
     (plus a special case for zero). High half of the new number comes 
     first. 
 *)

 Inductive zn2z : Set :=
  | W0 : zn2z
  | WW : znz -> znz -> zn2z.

 Definition zn2z_to_Z (wB:Z) (w_to_Z:znz->Z) (x:zn2z) :=
  match x with
  | W0 => 0
  | WW xh xl => w_to_Z xh * wB + w_to_Z xl
  end.

End Zn2Z.

Implicit Arguments W0 [znz].

(** From a cyclic representation [w], we iterate the [zn2z] construct 
    [n] times, gaining the type of binary trees of depth at most [n], 
    whose leafs are either W0 (if depth < n) or elements of w 
    (if depth = n). 
*)

Fixpoint word (w:Set) (n:nat) {struct n} : Set :=
 match n with
 | O => w
 | S n => zn2z (word w n)
 end.

