(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import QArith Qpower Qminmax.

Open Scope Q_scope.

(** * QSig *)

(** Interface of a rich structure about rational numbers.
    Specifications are written via translation to Q.
*)

Module Type QType.

 Parameter t : Type.

 Parameter to_Q : t -> Q.
 Notation "[ x ]" := (to_Q x).

 Definition eq x y := [x] == [y].
 Definition lt x y := [x] < [y].
 Definition le x y := [x] <= [y].

 Parameter of_Q : Q -> t.
 Parameter spec_of_Q: forall x, to_Q (of_Q x) == x.

 Parameter red : t -> t.
 Parameter compare : t -> t -> comparison.
 Parameter eq_bool : t -> t -> bool.
 Parameter max : t -> t -> t.
 Parameter min : t -> t -> t.
 Parameter zero : t.
 Parameter one : t.
 Parameter minus_one : t.
 Parameter add : t -> t -> t.
 Parameter sub : t -> t -> t.
 Parameter opp : t -> t.
 Parameter mul : t -> t -> t.
 Parameter square : t -> t.
 Parameter inv : t -> t.
 Parameter div : t -> t -> t.
 Parameter power : t -> Z -> t.

 Parameter spec_red : forall x, [red x] == [x].
 Parameter strong_spec_red : forall x, [red x] = Qred [x].
 Parameter spec_compare : forall x y, compare x y = ([x] ?= [y]).
 Parameter spec_eq_bool : forall x y, eq_bool x y = Qeq_bool [x] [y].
 Parameter spec_max : forall x y, [max x y] == Qmax [x] [y].
 Parameter spec_min : forall x y, [min x y] == Qmin [x] [y].
 Parameter spec_0: [zero] == 0.
 Parameter spec_1: [one] == 1.
 Parameter spec_m1: [minus_one] == -(1).
 Parameter spec_add: forall x y, [add x y] == [x] + [y].
 Parameter spec_sub: forall x y, [sub x y] == [x] - [y].
 Parameter spec_opp: forall x, [opp x] == - [x].
 Parameter spec_mul: forall x y, [mul x y] == [x] * [y].
 Parameter spec_square: forall x, [square x] == [x] ^ 2.
 Parameter spec_inv : forall x, [inv x] == / [x].
 Parameter spec_div: forall x y, [div x y] == [x] / [y].
 Parameter spec_power: forall x z, [power x z] == [x] ^ z.

End QType.

(** NB: several of the above functions come with [..._norm] variants
     that expect reduced arguments and return reduced results. *)

(** TODO : also speak of specifications via Qcanon ... *)
