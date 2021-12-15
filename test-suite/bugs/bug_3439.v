Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 3154 lines to 149 lines, then from 89 lines to 55 lines, then from 44 lines to 20 lines *)
Set Primitive Projections.
Generalizable All Variables.
Axiom IsHSet : Type -> Type.
Existing Class IsHSet.
Record PreCategory := { object :> Type }.
Notation IsStrictCategory C := (IsHSet (object C)).
Instance trunc_prod `{IsHSet A} `{IsHSet B} : IsHSet (A * B) | 100.
admit.
Defined.
Typeclasses Transparent object.
Definition prod (C D : PreCategory) : PreCategory := Build_PreCategory (Datatypes.prod C D).
Global Instance isstrict_category_product `{IsStrictCategory C, IsStrictCategory D} : IsStrictCategory (prod C D).
Proof.
  typeclasses eauto.
Defined.


Set Typeclasses Debug.
(* File reduced by coq-bug-finder from original input, then from 7425 lines to 154 lines, then from 116 lines to 20 lines *)
Class Contr (A : Type) := { center : A }.
Instance contr_unit : Contr unit | 0 := {| center := tt |}.
Module non_prim.
  Unset Primitive Projections.
  Record PreCategory := { object :> Type }.
  Lemma foo : Contr (object (@Build_PreCategory unit)).
  Proof.
    solve [ simpl; typeclasses eauto ] || fail "goal not solved".
    Undo.
    solve [ typeclasses eauto ].
  Defined.
End non_prim.

Module prim.
  Set Primitive Projections.
  Record PreCategory := { object :> Type }.
  Lemma foo : Contr (object (@Build_PreCategory unit)).
  Proof.
    solve [ simpl; typeclasses eauto ] || fail "goal not solved".
    Undo.
    solve [ typeclasses eauto ]. (*  Error: No applicable tactic. *)
  Defined.
End prim.
