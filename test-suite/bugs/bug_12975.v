Record foo :=
{
  myprop : Type;
}.

Set Primitive Projections.

Record bar :=
{
  myotherprop : Type ;
  someprop : myotherprop;
  somefn : myotherprop -> myotherprop
}.


Existing Class myprop.
Existing Class myotherprop.

#[export] Instance : forall O, myprop O. Abort.
#[export] Instance : forall (O : bar), myotherprop O.
Proof.
  intros O. destruct O; cbn. exact someprop0.
Defined.

Definition bar_nat : bar := {| myotherprop := nat; someprop := 0; somefn x := x |}.

Definition overloaded {b : bar} (o : myotherprop b) : myotherprop b :=
  somefn _ (someprop _).

Global Instance defaultbar_nat : myotherprop bar_nat := 0.

Type (_ : myotherprop bar_nat).
