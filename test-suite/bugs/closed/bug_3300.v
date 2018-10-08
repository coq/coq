Set Primitive Projections.
Record Box (T : Type) : Prop := wrap {prop : T}.

Definition down (x : Type) : Prop := Box x.
Definition up (x : Prop) : Type := x.

Fail Definition back A : up (down A) -> A := @prop A.
