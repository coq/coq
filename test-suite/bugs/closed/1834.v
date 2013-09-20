(* This tests rather deep nesting of abstracted terms *)

(* This used to fail before Nov 2011 because of a de Bruijn indice bug
   in extract_predicate.

   Note: use of eq_ok allows shorten notations but was not in the
   original example
*)

Scheme eq_rec_dep := Induction for eq Sort Type.

Section Teq.

Variable P0:           Type.
Variable P1: forall (y0:P0), Type.
Variable P2: forall y0 (y1:P1 y0), Type.
Variable P3: forall y0 y1 (y2:P2 y0 y1), Type.
Variable P4: forall y0 y1 y2 (y3:P3 y0 y1 y2), Type.
Variable P5: forall y0 y1 y2 y3 (y4:P4 y0 y1 y2 y3), Type.

Variable x0:P0.

Inductive eq0 : P0 -> Prop :=
  refl0: eq0 x0.

Definition eq_0 y0 := x0 = y0.

Variable x1:P1 x0.

Inductive eq1 : forall y0, P1 y0 -> Prop :=
  refl1: eq1 x0 x1.

Definition S0_0 y0 (e0:eq_0 y0) :=
  eq_rec_dep P0 x0 (fun y0 e0 => P1 y0) x1 y0 e0.

Definition eq_ok0 y0 y1 (E: eq_0 y0) := S0_0 y0 E = y1.

Definition eq_1 y0 y1 :=
  {E0:eq_0 y0 | eq_ok0 y0 y1 E0}.

Variable x2:P2 x0 x1.

Inductive eq2 :
forall y0 y1, P2 y0 y1 -> Prop :=
refl2: eq2 x0 x1 x2.

Definition S1_0 y0 (e0:eq_0 y0) :=
eq_rec_dep P0 x0 (fun y0 e0 => P2 y0 (S0_0 y0 e0)) x2 y0 e0.

Definition S1_1 y0 y1 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1) :=
  eq_rec_dep (P1 y0) (S0_0 y0 e0) (fun y1 e1 => P2 y0 y1)
   (S1_0 y0 e0)
   y1 e1.

Definition eq_ok1 y0 y1 y2 (E: eq_1 y0 y1) :=
  match E with exist _ e0 e1 => S1_1 y0 y1 e0 e1 = y2 end.

Definition eq_2 y0 y1 y2 :=
  {E1:eq_1 y0 y1 | eq_ok1 y0 y1 y2 E1}.

Variable x3:P3 x0 x1 x2.

Inductive eq3 :
forall y0 y1 y2, P3 y0 y1 y2 -> Prop :=
refl3: eq3 x0 x1 x2 x3.

Definition S2_0 y0 (e0:eq_0 y0) :=
eq_rec_dep P0 x0 (fun y0 e0 => P3 y0 (S0_0 y0 e0) (S1_0 y0 e0)) x3 y0 e0.

Definition S2_1 y0 y1 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1) :=
  eq_rec_dep (P1 y0) (S0_0 y0 e0)
   (fun y1 e1 => P3 y0 y1 (S1_1 y0 y1 e0 e1))
   (S2_0 y0 e0)
   y1 e1.

Definition S2_2 y0 y1 y2 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1)
  (e2:S1_1 y0 y1 e0 e1 = y2) :=
  eq_rec_dep (P2 y0 y1) (S1_1 y0 y1 e0 e1)
   (fun y2 e2 => P3 y0 y1 y2)
   (S2_1 y0 y1 e0 e1)
   y2 e2.

Definition eq_ok2 y0 y1 y2 y3 (E: eq_2 y0 y1 y2) : Prop :=
  match E with exist _ (exist _ e0 e1) e2 =>
     S2_2 y0 y1 y2 e0 e1 e2 = y3 end.

Definition eq_3 y0 y1 y2 y3 :=
  {E2: eq_2 y0 y1 y2 | eq_ok2 y0 y1 y2 y3 E2}.

Variable x4:P4 x0 x1 x2 x3.

Inductive eq4 :
forall y0 y1 y2 y3, P4 y0 y1 y2 y3 -> Prop :=
refl4: eq4 x0 x1 x2 x3 x4.

Definition S3_0 y0 (e0:eq_0 y0) :=
eq_rec_dep P0 x0 (fun y0 e0 => P4 y0 (S0_0 y0 e0) (S1_0 y0 e0) (S2_0 y0 e0))
  x4 y0 e0.

Definition S3_1 y0 y1 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1) :=
  eq_rec_dep (P1 y0) (S0_0 y0 e0)
   (fun y1 e1 => P4 y0 y1 (S1_1 y0 y1 e0 e1) (S2_1 y0 y1 e0 e1))
   (S3_0 y0 e0)
   y1 e1.

Definition S3_2 y0 y1 y2 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1)
  (e2:S1_1 y0 y1 e0 e1 = y2) :=
  eq_rec_dep (P2 y0 y1) (S1_1 y0 y1 e0 e1)
   (fun y2 e2 => P4 y0 y1 y2 (S2_2 y0 y1 y2 e0 e1 e2))
   (S3_1 y0 y1 e0 e1)
   y2 e2.

Definition S3_3 y0 y1 y2 y3 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1)
  (e2:S1_1 y0 y1 e0 e1 = y2) (e3:S2_2 y0 y1 y2 e0 e1 e2 = y3):=
  eq_rec_dep (P3 y0 y1 y2) (S2_2 y0 y1 y2 e0 e1 e2)
   (fun y3 e3 => P4 y0 y1 y2 y3)
   (S3_2 y0 y1 y2 e0 e1 e2)
   y3 e3.

Definition eq_ok3 y0 y1 y2 y3 y4 (E: eq_3 y0 y1 y2 y3) : Prop :=
  match E with exist _ (exist _ (exist _ e0 e1) e2) e3 =>
     S3_3 y0 y1 y2 y3 e0 e1 e2 e3 = y4 end.

Definition eq_4 y0 y1 y2 y3 y4 :=
  {E3: eq_3 y0 y1 y2 y3 | eq_ok3 y0 y1 y2 y3 y4 E3}.

Variable x5:P5 x0 x1 x2 x3 x4.

Inductive eq5 :
forall y0 y1 y2 y3 y4, P5 y0 y1 y2 y3 y4 -> Prop :=
refl5: eq5 x0 x1 x2 x3 x4 x5.

Definition S4_0 y0 (e0:eq_0 y0) :=
eq_rec_dep P0 x0
(fun y0 e0 => P5 y0 (S0_0 y0 e0) (S1_0 y0 e0) (S2_0 y0 e0) (S3_0 y0 e0))
  x5 y0 e0.

Definition S4_1 y0 y1 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1) :=
  eq_rec_dep (P1 y0) (S0_0 y0 e0)
   (fun y1 e1 => P5 y0 y1 (S1_1 y0 y1 e0 e1) (S2_1 y0 y1 e0 e1) (S3_1 y0 y1 e0
e1))
   (S4_0 y0 e0)
   y1 e1.

Definition S4_2 y0 y1 y2 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1)
  (e2:S1_1 y0 y1 e0 e1 = y2) :=
  eq_rec_dep (P2 y0 y1) (S1_1 y0 y1 e0 e1)
   (fun y2 e2 => P5 y0 y1 y2 (S2_2 y0 y1 y2 e0 e1 e2) (S3_2 y0 y1 y2 e0 e1 e2))
   (S4_1 y0 y1 e0 e1)
   y2 e2.

Definition S4_3 y0 y1 y2 y3 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1)
  (e2:S1_1 y0 y1 e0 e1 = y2) (e3:S2_2 y0 y1 y2 e0 e1 e2 = y3):=
  eq_rec_dep (P3 y0 y1 y2) (S2_2 y0 y1 y2 e0 e1 e2)
   (fun y3 e3 => P5 y0 y1 y2 y3 (S3_3 y0 y1 y2 y3 e0 e1 e2 e3))
   (S4_2 y0 y1 y2 e0 e1 e2)
   y3 e3.

Definition S4_4 y0 y1 y2 y3 y4 (e0:eq_0 y0) (e1:S0_0 y0 e0 = y1)
  (e2:S1_1 y0 y1 e0 e1 = y2) (e3:S2_2 y0 y1 y2 e0 e1 e2 = y3)
  (e4:S3_3 y0 y1 y2 y3 e0 e1 e2 e3 = y4) :=
  eq_rec_dep (P4 y0 y1 y2 y3) (S3_3 y0 y1 y2 y3 e0 e1 e2 e3)
   (fun y4 e4 => P5 y0 y1 y2 y3 y4)
   (S4_3 y0 y1 y2 y3 e0 e1 e2 e3)
   y4 e4.

Definition eq_ok4 y0 y1 y2 y3 y4 y5 (E: eq_4 y0 y1 y2 y3 y4) : Prop :=
  match E with exist _ (exist _ (exist _ (exist _ e0 e1) e2) e3) e4 =>
     S4_4 y0 y1 y2 y3 y4 e0 e1 e2 e3 e4 = y5 end.

Definition eq_5 y0 y1 y2 y3 y4 y5 :=
  {E4: eq_4 y0 y1 y2 y3 y4 | eq_ok4 y0 y1 y2 y3 y4 y5 E4 }.

End Teq.
