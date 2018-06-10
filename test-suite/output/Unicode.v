Require Import Coq.Unicode.Utf8.

Section test.
Context (very_very_long_type_name1 : Type) (very_very_long_type_name2 : Type).
Context (f : very_very_long_type_name1 -> very_very_long_type_name2 -> Prop).

Lemma test : True -> True ->
  forall (x : very_very_long_type_name1) (y : very_very_long_type_name2),
    f x y /\ f x y /\ f x y /\ f x y /\ f x y /\ f x y.
Proof. Show. Abort.

Lemma test : True -> True ->
  forall (x : very_very_long_type_name2) (y : very_very_long_type_name1)
         (z : very_very_long_type_name2),
    f y x /\ f y z.
Proof. Show. Abort.

Lemma test : True -> True ->
  forall (x : very_very_long_type_name2) (y : very_very_long_type_name1)
         (z : very_very_long_type_name2),
    f y x /\ f y z /\ f y x /\ f y z /\ f y x /\ f y z.
Proof. Show. Abort.

Lemma test : True -> True ->
  exists (x : very_very_long_type_name1) (y : very_very_long_type_name2),
    f x y /\ f x y /\ f x y /\ f x y /\ f x y /\ f x y.
Proof. Show. Abort.
End test.
