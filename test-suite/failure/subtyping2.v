(* Check that no constraints on inductive types disappear at subtyping *)

Module Type S.

Record A0 : Type :=  (* Type_i' *)
  i0 {X0 : Type; R0 : X0 -> X0 -> Prop}. (* X0: Type_j' *)

Variable i0' : forall X0 : Type, (X0 -> X0 -> Prop) -> A0.

End S.

Module M.

Record A0 : Type :=  (* Type_i' *)
  i0 {X0 : Type; R0 : X0 -> X0 -> Prop}. (* X0: Type_j' *)

Definition i0' := i0 : forall X0 : Type, (X0 -> X0 -> Prop) -> A0.

End M.

(* The rest of this file formalizes Burali-Forti paradox *)
(* (if the constraint between i0' and A0 is lost, the proof goes through) *)

  Inductive ACC (A : Type) (R : A -> A -> Prop) : A -> Prop :=
      ACC_intro :
        forall x : A, (forall y : A, R y x -> ACC A R y) -> ACC A R x.

  Lemma ACC_nonreflexive :
   forall (A : Type) (R : A -> A -> Prop) (x : A),
   ACC A R x -> R x x -> False.
simple induction 1; intros.
exact (H1 x0 H2 H2).
Qed.

  Definition WF (A : Type) (R : A -> A -> Prop) := forall x : A, ACC A R x.


Section Inverse_Image.

  Variables (A B : Type) (R : B -> B -> Prop) (f : A -> B).

  Definition Rof (x y : A) : Prop := R (f x) (f y).

  Remark ACC_lemma :
   forall y : B, ACC B R y -> forall x : A, y = f x -> ACC A Rof x.
    simple induction 1; intros.
    constructor; intros.
    apply (H1 (f y0)); trivial.
    elim H2 using eq_ind_r; trivial.
    Qed.

  Lemma ACC_inverse_image : forall x : A, ACC B R (f x) -> ACC A Rof x.
    intros; apply (ACC_lemma (f x)); trivial.
    Qed.

  Lemma WF_inverse_image : WF B R -> WF A Rof.
    red; intros; apply ACC_inverse_image; auto.
    Qed.

End Inverse_Image.

Section Burali_Forti_Paradox.

  Definition morphism (A : Type) (R : A -> A -> Prop)
    (B : Type) (S : B -> B -> Prop) (f : A -> B) :=
    forall x y : A, R x y -> S (f x) (f y).

  (* The hypothesis of the paradox:
     assumes there exists an universal system of notations, i.e:
      - A type A0
      - An injection i0 from relations on any type into A0
      - The proof that i0 is injective modulo morphism
   *)
  Variable A0 : Type.                     (* Type_i *)
  Variable i0 : forall X : Type, (X -> X -> Prop) -> A0. (* X: Type_j *)
  Hypothesis
    inj :
      forall (X1 : Type) (R1 : X1 -> X1 -> Prop) (X2 : Type)
        (R2 : X2 -> X2 -> Prop),
      i0 X1 R1 = i0 X2 R2 -> exists f : X1 -> X2, morphism X1 R1 X2 R2 f.

  (* Embedding of x in y: x and y are images of 2 well founded relations
     R1 and R2, the ordinal of R2 being strictly greater than that of R1.
   *)
  Record emb (x y : A0) : Prop :=
    {X1 : Type;
     R1 : X1 -> X1 -> Prop;
     eqx : x = i0 X1 R1;
     X2 : Type;
     R2 : X2 -> X2 -> Prop;
     eqy : y = i0 X2 R2;
     W2 : WF X2 R2;
     f : X1 -> X2;
     fmorph : morphism X1 R1 X2 R2 f;
     maj : X2;
     majf : forall z : X1, R2 (f z) maj}.


  Lemma emb_trans : forall x y z : A0, emb x y -> emb y z -> emb x z.
intros.
case H; intros.
case H0; intros.
generalize eqx0; clear eqx0.
elim eqy using eq_ind_r; intro.
case (inj _ _ _ _ eqx0); intros.
exists X1 R1 X3 R3 (fun x : X1 => f0 (x0 (f x))) maj0; trivial.
red; auto.
Defined.


  Lemma ACC_emb :
   forall (X : Type) (R : X -> X -> Prop) (x : X),
   ACC X R x ->
   forall (Y : Type) (S : Y -> Y -> Prop) (f : Y -> X),
   morphism Y S X R f -> (forall y : Y, R (f y) x) -> ACC A0 emb (i0 Y S).
simple induction 1; intros.
constructor; intros.
case H4; intros.
elim eqx using eq_ind_r.
case (inj X2 R2 Y S).
apply sym_eq; assumption.

intros.
apply H1 with (y := f (x1 maj)) (f := fun x : X1 => f (x1 (f0 x)));
 try red; auto.
Defined.

  (* The embedding relation is well founded *)
  Lemma WF_emb : WF A0 emb.
constructor; intros.
case H; intros.
elim eqx using eq_ind_r.
apply ACC_emb with (X := X2) (R := R2) (x := maj) (f := f); trivial.
Defined.


  (* The following definition enforces Type_j >= Type_i *)
  Definition Omega : A0 := i0 A0 emb.


Section Subsets.

  Variable a : A0.

  (* We define the type of elements of A0 smaller than a w.r.t embedding.
     The Record is in Type, but it is possible to avoid such structure. *)
  Record sub : Type :=  {witness : A0; emb_wit : emb witness a}.

  (* F is its image through i0 *)
  Definition F : A0 := i0 sub (Rof _ _ emb witness).

  (* F is embedded in Omega:
     - the witness projection is a morphism
     - a is an upper bound because emb_wit proves that witness is
       smaller than a.
   *)
  Lemma F_emb_Omega : emb F Omega.
exists sub (Rof _ _ emb witness) A0 emb witness a; trivial.
exact WF_emb.

red; trivial.

exact emb_wit.
Defined.

End Subsets.


  Definition fsub (a b : A0) (H : emb a b) (x : sub a) :
    sub b := Build_sub _ (witness _ x) (emb_trans _ _ _ (emb_wit _ x) H).

  (* F is a morphism: a < b => F(a) < F(b)
      - the morphism from F(a) to F(b) is fsub above
      - the upper bound is a, which is in F(b) since a < b
   *)
  Lemma F_morphism : morphism A0 emb A0 emb F.
red; intros.
exists
 (sub x)
   (Rof _ _ emb (witness x))
   (sub y)
   (Rof _ _ emb (witness y))
   (fsub x y H)
   (Build_sub _ x H); trivial.
apply WF_inverse_image.
exact WF_emb.

unfold morphism, Rof, fsub; simpl; intros.
trivial.

unfold Rof, fsub; simpl; intros.
apply emb_wit.
Defined.


  (* Omega is embedded in itself:
     - F is a morphism
     - Omega is an upper bound of the image of F
   *)
  Lemma Omega_refl : emb Omega Omega.
exists A0 emb A0 emb F Omega; trivial.
exact WF_emb.

exact F_morphism.

exact F_emb_Omega.
Defined.

  (* The paradox is that Omega cannot be embedded in itself, since
     the embedding relation is well founded.
   *)
  Theorem Burali_Forti : False.
apply ACC_nonreflexive with A0 emb Omega.
apply WF_emb.

exact Omega_refl.

Defined.

End Burali_Forti_Paradox.

Import M.

  (* Note: this proof uses a large elimination of A0. *)
  Lemma inj :
   forall (X1 : Type) (R1 : X1 -> X1 -> Prop) (X2 : Type)
     (R2 : X2 -> X2 -> Prop),
   i0' X1 R1 = i0' X2 R2 -> exists f : X1 -> X2, morphism X1 R1 X2 R2 f.
intros.
change
  match i0' X1 R1, i0' X2 R2 with
  | i0 x1 r1, i0 x2 r2 => exists f : _, morphism x1 r1 x2 r2 f
  end.
case H; simpl.
exists (fun x : X1 => x).
red; trivial.
Defined.

(* The following command raises 'Error: Universe Inconsistency'.
   To allow large elimination of A0, i0 must not be a large constructor.
   Hence, the constraint Type_j' < Type_i' is added, which is incompatible
   with the constraint j >= i in the paradox.
*)

  Fail Definition Paradox : False := Burali_Forti A0 i0' inj.
