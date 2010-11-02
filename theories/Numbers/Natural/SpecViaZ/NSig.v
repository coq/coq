(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import ZArith Znumtheory.

Open Scope Z_scope.

(** * NSig *)

(** Interface of a rich structure about natural numbers.
    Specifications are written via translation to Z.
*)

Module Type NType.

 Parameter t : Type.

 Parameter to_Z : t -> Z.
 Local Notation "[ x ]" := (to_Z x).
 Parameter spec_pos: forall x, 0 <= [x].

 Parameter of_N : N -> t.
 Parameter spec_of_N: forall x, to_Z (of_N x) = Z_of_N x.
 Definition to_N n := Zabs_N (to_Z n).

 Definition eq n m := [n] = [m].
 Definition lt n m := [n] < [m].
 Definition le n m := [n] <= [m].

 Parameter compare : t -> t -> comparison.
 Parameter eq_bool : t -> t -> bool.
 Parameter max : t -> t -> t.
 Parameter min : t -> t -> t.
 Parameter zero : t.
 Parameter one : t.
 Parameter two : t.
 Parameter succ : t -> t.
 Parameter pred : t -> t.
 Parameter add  : t -> t -> t.
 Parameter sub : t -> t -> t.
 Parameter mul : t -> t -> t.
 Parameter square : t -> t.
 Parameter pow_pos : t -> positive -> t.
 Parameter pow_N : t -> N -> t.
 Parameter pow : t -> t -> t.
 Parameter sqrt : t -> t.
 Parameter log2 : t -> t.
 Parameter div_eucl : t -> t -> t * t.
 Parameter div : t -> t -> t.
 Parameter modulo : t -> t -> t.
 Parameter gcd : t -> t -> t.
 Parameter shiftr : t -> t -> t.
 Parameter shiftl : t -> t -> t.
 Parameter even : t -> bool.
 Parameter odd : t -> bool.

 Parameter spec_compare: forall x y, compare x y = Zcompare [x] [y].
 Parameter spec_eq_bool: forall x y, eq_bool x y = Zeq_bool [x] [y].
 Parameter spec_max : forall x y, [max x y] = Zmax [x] [y].
 Parameter spec_min : forall x y, [min x y] = Zmin [x] [y].
 Parameter spec_0: [zero] = 0.
 Parameter spec_1: [one] = 1.
 Parameter spec_2: [two] = 2.
 Parameter spec_succ: forall n, [succ n] = [n] + 1.
 Parameter spec_add: forall x y, [add x y] = [x] + [y].
 Parameter spec_pred: forall x, [pred x] = Zmax 0 ([x] - 1).
 Parameter spec_sub: forall x y, [sub x y] = Zmax 0 ([x] - [y]).
 Parameter spec_mul: forall x y, [mul x y] = [x] * [y].
 Parameter spec_square: forall x, [square x] = [x] *  [x].
 Parameter spec_pow_pos: forall x n, [pow_pos x n] = [x] ^ Zpos n.
 Parameter spec_pow_N: forall x n, [pow_N x n] = [x] ^ Z_of_N n.
 Parameter spec_pow: forall x n, [pow x n] = [x] ^ [n].
 Parameter spec_sqrt: forall x, [sqrt x] = Zsqrt [x].
 Parameter spec_log2: forall x, [log2 x] = Zlog2 [x].
 Parameter spec_div_eucl: forall x y,
  let (q,r) := div_eucl x y in ([q], [r]) = Zdiv_eucl [x] [y].
 Parameter spec_div: forall x y, [div x y] = [x] / [y].
 Parameter spec_modulo: forall x y, [modulo x y] = [x] mod [y].
 Parameter spec_gcd: forall a b, [gcd a b] = Zgcd [a] [b].
 Parameter spec_shiftr: forall p x, [shiftr p x] = [x] / 2^[p].
 Parameter spec_shiftl: forall p x, [shiftl p x] = [x] * 2^[p].
 Parameter spec_even: forall x, even x = Zeven_bool [x].
 Parameter spec_odd: forall x, odd x = Zodd_bool [x].

End NType.

Module Type NType_Notation (Import N:NType).
 Notation "[ x ]" := (to_Z x).
 Infix "==" := eq (at level 70).
 Notation "0" := zero.
 Notation "1" := one.
 Notation "2" := two.
 Infix "+" := add.
 Infix "-" := sub.
 Infix "*" := mul.
 Infix "^" := pow.
 Infix "<=" := le.
 Infix "<" := lt.
End NType_Notation.

Module Type NType' := NType <+ NType_Notation.
