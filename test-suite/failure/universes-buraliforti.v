(* Check that Burali-Forti paradox does not go through *)

(* Source: contrib/Rocq/PARADOX/{Logics,BuraliForti},v *)

(* Some properties about relations on objects in Type *)

  Inductive ACC [A : Type; R : A->A->Prop] : A->Prop :=
      ACC_intro : (x:A)((y:A)(R y x)->(ACC A R y))->(ACC A R x).

  Lemma ACC_nonreflexive:
    (A:Type)(R:A->A->Prop)(x:A)(ACC A R x)->(R x x)->False.
Induction 1; Intros.
Exact (H1 x0 H2 H2).
Save.

  Definition WF := [A:Type][R:A->A->Prop](x:A)(ACC A R x).


Section Inverse_Image.

  Variables A,B:Type; R:B->B->Prop; f:A->B.

  Definition Rof : A->A->Prop := [x,y:A](R (f x) (f y)).

  Remark ACC_lemma : (y:B)(ACC B R y)->(x:A)(y==(f x))->(ACC A Rof x).
    Induction 1; Intros.
    Constructor; Intros.
    Apply (H1 (f y0)); Trivial.
    Elim H2 using eqT_ind_r; Trivial.
    Save.

  Lemma ACC_inverse_image : (x:A)(ACC B R (f x)) -> (ACC A Rof x).
    Intros; Apply (ACC_lemma (f x)); Trivial.
    Save.

  Lemma WF_inverse_image: (WF B R)->(WF A Rof).
    Red; Intros; Apply ACC_inverse_image; Auto.
    Save.

End Inverse_Image.


(* Remark: the paradox is written in Type, but also works in Prop or Set. *)

Section Burali_Forti_Paradox.

  Definition morphism := [A:Type][R:A->A->Prop][B:Type][S:B->B->Prop][f:A->B]
    (x,y:A)(R x y)->(S (f x) (f y)).

  (* The hypothesis of the paradox:
     assumes there exists an universal system of notations, i.e:
      - A type A0
      - An injection i0 from relations on any type into A0
      - The proof that i0 is injective modulo morphism 
   *)
  Variable   A0  : Type.                     (* Type_i *)
  Variable   i0  : (X:Type)(X->X->Prop)->A0. (* X: Type_j *)
  Hypothesis inj : (X1:Type)(R1:X1->X1->Prop)(X2:Type)(R2:X2->X2->Prop)
                     (i0 X1 R1)==(i0 X2 R2)
                       ->(EXT f:X1->X2 | (morphism X1 R1 X2 R2 f)).

  (* Embedding of x in y: x and y are images of 2 well founded relations
     R1 and R2, the ordinal of R2 being strictly greater than that of R1.
   *)
  Record emb [x,y:A0]: Prop := {
    X1: Type;
    R1: X1->X1->Prop;
    eqx: x==(i0 X1 R1);
    X2: Type;
    R2: X2->X2->Prop;
    eqy: y==(i0 X2 R2);
    W2: (WF X2 R2);
    f: X1->X2;
    fmorph: (morphism X1 R1 X2 R2 f);
    maj: X2;
    majf: (z:X1)(R2 (f z) maj) }.


  Lemma emb_trans: (x,y,z:A0)(emb x y)->(emb y z)->(emb x z).
Intros.
Case H; Intros.
Case H0; Intros.
Generalize eqx0; Clear eqx0.
Elim eqy using eqT_ind_r; Intro.
Case (inj ? ? ? ? eqx0); Intros.
Exists X1 R1 X3 R3 [x:X1](f0 (x0 (f x))) maj0; Trivial.
Red; Auto.
Defined.


  Lemma ACC_emb: (X:Type)(R:X->X->Prop)(x:X)(ACC X R x)
    ->(Y:Type)(S:Y->Y->Prop)(f:Y->X)(morphism Y S X R f)
      ->((y:Y)(R (f y) x))
        ->(ACC A0 emb (i0 Y S)).
Induction 1; Intros.
Constructor; Intros.
Case H4; Intros.
Elim eqx using eqT_ind_r.
Case (inj X2 R2 Y S).
Apply sym_eqT; Assumption.

Intros.
Apply H1 with y:=(f (x1 maj)) f:=[x:X1](f (x1 (f0 x))); Try Red; Auto.
Defined.

  (* The embedding relation is well founded *)
  Lemma WF_emb: (WF A0 emb).
Constructor; Intros.
Case H; Intros.
Elim eqx using eqT_ind_r.
Apply ACC_emb with X:=X2 R:=R2 x:=maj f:=f; Trivial.
Defined.


  (* The following definition enforces Type_j >= Type_i *)
  Definition Omega: A0 := (i0 A0 emb).


Section Subsets.

  Variable a: A0.

  (* We define the type of elements of A0 smaller than a w.r.t embedding.
     The Record is in Type, but it is possible to avoid such structure. *)
  Record sub: Type := {
    witness : A0;
    emb_wit : (emb witness a) }.

  (* F is its image through i0 *)
  Definition F : A0 := (i0 sub (Rof ? ? emb witness)).

  (* F is embedded in Omega:
     - the witness projection is a morphism
     - a is an upper bound because emb_wit proves that witness is
       smaller than a.
   *)
  Lemma F_emb_Omega: (emb F Omega).
Exists sub (Rof ? ? emb witness) A0 emb witness a; Trivial.
Exact WF_emb.

Red; Trivial.

Exact emb_wit.
Defined.

End Subsets.


  Definition fsub: (a,b:A0)(emb a b)->(sub a)->(sub b):=
    [_,_][H][x]
      (Build_sub ? (witness ? x) (emb_trans ? ? ? (emb_wit ? x) H)).

  (* F is a morphism: a < b => F(a) < F(b)
      - the morphism from F(a) to F(b) is fsub above
      - the upper bound is a, which is in F(b) since a < b
   *)
  Lemma F_morphism: (morphism A0 emb A0 emb F).
Red; Intros.
Exists (sub x) (Rof ? ? emb (witness x)) (sub y)
       (Rof ? ? emb (witness y)) (fsub x y H) (Build_sub ? x H); 
Trivial.
Apply WF_inverse_image.
Exact WF_emb.

Unfold morphism Rof fsub; Simpl; Intros.
Trivial.

Unfold Rof fsub; Simpl; Intros.
Apply emb_wit.
Defined.


  (* Omega is embedded in itself:
     - F is a morphism
     - Omega is an upper bound of the image of F
   *)
  Lemma Omega_refl: (emb Omega Omega).
Exists A0 emb A0 emb F Omega; Trivial.
Exact WF_emb.

Exact F_morphism.

Exact F_emb_Omega.
Defined.

  (* The paradox is that Omega cannot be embedded in itself, since
     the embedding relation is well founded.
   *)
  Theorem Burali_Forti: False.
Apply ACC_nonreflexive with A0 emb Omega.
Apply WF_emb.

Exact Omega_refl.

Defined.

End Burali_Forti_Paradox.


  (* The following type seems to satisfy the hypothesis of the paradox.
     But it does not!
   *)
  Record A0: Type := (* Type_i' *)
    i0 { X0: Type; R0: X0->X0->Prop }. (* X0: Type_j' *)


  (* Note: this proof uses a large elimination of A0. *)
  Lemma inj : (X1:Type)(R1:X1->X1->Prop)(X2:Type)(R2:X2->X2->Prop)
                    (i0 X1 R1)==(i0 X2 R2)
                      ->(EXT f:X1->X2 | (morphism X1 R1 X2 R2 f)).
Intros.
Change Cases (i0 X1 R1) (i0 X2 R2) of
         (i0 x1 r1) (i0 x2 r2) => (EXT f | (morphism x1 r1 x2 r2 f))
       end.
Case H; Simpl.
Exists [x:X1]x.
Red; Trivial.
Defined.

(* The following command raises 'Error: Universe Inconsistency'.
   To allow large elimination of A0, i0 must not be a large constructor.
   Hence, the constraint Type_j' < Type_i' is added, which is incompatible
   with the constraint j >= i in the paradox.
*)

  Definition Paradox: False := (Burali_Forti A0 i0 inj).

