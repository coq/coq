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

Require Import ZArith Znumtheory.

Open Scope Z_scope.

(** * NSig *)

(** Interface of a rich structure about natural numbers.
    Specifications are written via translation to Z.
*)

Module Type NType.

 Parameter t : Type.

 Parameter to_Z : t -> Z.
 Notation "[ x ]" := (to_Z x).
 Parameter spec_pos: forall x, 0 <= [x].

 Parameter of_N : N -> t.
 Parameter spec_of_N: forall x, to_Z (of_N x) = Z_of_N x.
 Definition to_N n := Zabs_N (to_Z n).

 Definition eq n m := ([n] = [m]).

 Parameter zero : t.
 Parameter one : t.

 Parameter spec_0: [zero] = 0.
 Parameter spec_1: [one] = 1.

 Parameter compare : t -> t -> comparison.

 Parameter spec_compare: forall x y,
   match compare x y with
     | Eq => [x] = [y]
     | Lt => [x] < [y]
     | Gt => [x] > [y]
   end.

 Definition lt n m := compare n m = Lt.
 Definition le n m := compare n m <> Gt.
 Definition min n m := match compare n m with Gt => m | _ => n end.
 Definition max n m := match compare n m with Lt => m | _ => n end.

 Parameter eq_bool : t -> t -> bool.

 Parameter spec_eq_bool: forall x y,
    if eq_bool x y then [x] = [y] else [x] <> [y].

 Parameter succ : t -> t.

 Parameter spec_succ: forall n, [succ n] = [n] + 1.

 Parameter add  : t -> t -> t.

 Parameter spec_add: forall x y, [add x y] = [x] + [y].

 Parameter pred : t -> t.

 Parameter spec_pred: forall x, [pred x] = Zmax 0 ([x] - 1).

 Parameter sub : t -> t -> t.

 Parameter spec_sub: forall x y, [sub x y] = Zmax 0 ([x] - [y]).

 Parameter mul : t -> t -> t.

 Parameter spec_mul: forall x y, [mul x y] = [x] * [y].

 Parameter square : t -> t.

 Parameter spec_square: forall x, [square x] = [x] *  [x].

 Parameter power_pos : t -> positive -> t.

 Parameter spec_power_pos: forall x n, [power_pos x n] = [x] ^ Zpos n.

 Parameter sqrt : t -> t.

 Parameter spec_sqrt: forall x, [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.

 Parameter div_eucl : t -> t -> t * t.

 Parameter spec_div_eucl: forall x y,
  let (q,r) := div_eucl x y in ([q], [r]) = Zdiv_eucl [x] [y].

 Parameter div : t -> t -> t.

 Parameter spec_div: forall x y, [div x y] = [x] / [y].

 Parameter modulo : t -> t -> t.

 Parameter spec_modulo: forall x y, [modulo x y] = [x] mod [y].

 Parameter gcd : t -> t -> t.

 Parameter spec_gcd: forall a b, [gcd a b] = Zgcd (to_Z a) (to_Z b).

End NType.
