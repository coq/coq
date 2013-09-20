(* Error message was not printed in the correct environment *)

Fail Parameters (A:Prop) (a:A A).

(* This is a variant (reported as part of bug #2347) *)

Require Import EquivDec.                                              
Fail Program Instance bool_eq_eqdec : EqDec bool eq := 
   {equiv_dec x y := (fix aux (x y : bool) {struct x}:= aux _ y) x y}.

