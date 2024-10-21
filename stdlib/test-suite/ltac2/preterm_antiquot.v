From Stdlib Require Import ZArith.
Open Scope Z_scope.

From Stdlib Require Import Ltac2.Ltac2.

Ltac2 rec z2nat_preterm x :=
  let b := eval cbv in (Z.leb $x 0) in
  lazy_match! b with
  | true => preterm:(O)
  | false =>
      let pred := eval cbv in (Z.pred $x) in
        let r := z2nat_preterm pred in
        preterm:(S $preterm:r)
  end.


Ltac2 rec z2nat_constr x :=
  let b := eval cbv in (Z.leb $x 0) in
  lazy_match! b with
  | true => constr:(O)
  | false => let pred := eval cbv in (Z.pred $x) in
             let r := z2nat_constr pred in
             constr:(S $r)
  end.

Ltac2 mk_app(a: constr)(b: constr) :=
  Constr.Unsafe.make (Constr.Unsafe.App a [| b |]).

Ltac2 rec z2nat_mk_app x :=
  let b := eval cbv in (Z.leb $x 0) in
  lazy_match! b with
  | true => Env.instantiate reference:(O)
  | false => let pred := eval cbv in (Z.pred $x) in
             mk_app (Env.instantiate reference:(S)) (z2nat_mk_app pred)
  end.

(* Time Ltac2 Eval *)
(*   let c := z2nat_constr constr:(10000) in *)
(*   Message.print (Message.of_constr c). (* 9 secs *) *)

(* Time Ltac2 Eval *)
(*   let c := z2nat_mk_app constr:(10000) in *)
(*   Message.print (Message.of_constr c). (* <1 secs *) *)

Time Ltac2 Eval
  let c := z2nat_preterm constr:(10000) in
  let c := constr:($preterm:c) in
  Message.print (Message.of_constr c). (* 6 secs *)

(* Time Ltac2 Eval *)
(*   let c := z2nat_constr constr:(20000) in *)
(*   Message.print (Message.of_constr c). (* 22 secs *) *)

(* Time Ltac2 Eval *)
(*   let c := z2nat_mk_app constr:(20000) in *)
(*   Message.print (Message.of_constr c). (* 1.6 secs *) *)

(* a bit close to stack overflow *)
(* Time Ltac2 Eval *)
(*   let c := z2nat_preterm constr:(20000) in *)
(*   let c := Constr.pretype c in *)
(*   Message.print (Message.of_constr c). (* 32 secs *) *)
