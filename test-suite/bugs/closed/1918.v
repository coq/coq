(** Occur-check for Meta (up to delta) *)

(** LNMItPredShort.v Version 2.0 July 2008 *)
(** does not need impredicative Set, runs under V8.2, tested with SVN 11296 *)

(** Copyright Ralph Matthes, I.R.I.T.,  C.N.R.S. & University of Toulouse*)


Set Implicit Arguments.

(** the universe of all monotypes *)
Definition k0 := Set.

(** the type of all type transformations *)
Definition k1 := k0 -> k0.

(** the type of all rank-2 type transformations *)
Definition k2 := k1 -> k1.

(** polymorphic identity *)
Definition id : forall (A:Set), A -> A := fun A x => x.

(** composition *)
Definition comp (A B C:Set)(g:B->C)(f:A->B) : A->C := fun x => g (f x).

Infix "o" := comp (at level 90).

Definition sub_k1 (X Y:k1) : Type :=
     forall A:Set, X A -> Y A.

Infix "c_k1" := sub_k1 (at level 60).

(** monotonicity *)
Definition mon (X:k1) : Type := forall (A B:Set), (A -> B) -> X A -> X B.

(** extensionality *)
Definition ext (X:k1)(h: mon X): Prop :=
  forall (A B:Set)(f g:A -> B),
        (forall a, f a = g a) -> forall r, h _ _ f r = h _ _ g r.

(** first functor law *)
Definition fct1 (X:k1)(m: mon X) : Prop :=
  forall (A:Set)(x:X A), m _ _ (id(A:=A)) x = x.

(** second functor law *)
Definition fct2 (X:k1)(m: mon X) : Prop :=
 forall (A B C:Set)(f:A -> B)(g:B -> C)(x:X A),
       m _ _ (g o f) x = m _ _ g (m _ _ f x).

(** pack up the good properties of the approximation into
  the notion of an extensional functor *)
Record EFct (X:k1) : Type := mkEFct
  { m : mon X;
     e : ext m;
     f1 : fct1 m;
     f2 : fct2 m }.

(** preservation of extensional functors *)
Definition pEFct (F:k2) : Type :=
  forall (X:k1), EFct X -> EFct (F X).


(** we show some closure properties of pEFct, depending on such properties
      for EFct *)

Definition moncomp (X Y:k1)(mX:mon X)(mY:mon Y): mon (fun A => X(Y A)).
Proof.
  red.
  intros A B f x.
  exact (mX (Y A)(Y B) (mY A B f) x).
Defined.

(** closure under composition *)
Lemma compEFct (X Y:k1): EFct X -> EFct Y -> EFct (fun A => X(Y A)).
Proof.
  intros ef1 ef2.
  apply (mkEFct(m:=moncomp (m ef1) (m ef2))); red; intros; unfold moncomp.
(* prove ext *)
  apply (e ef1).
  intro.
  apply (e ef2); trivial.
(* prove fct1 *)
  rewrite (e ef1 (m ef2 (id (A:=A))) (id(A:=Y A))).
  apply (f1 ef1).
  intro.
  apply (f1 ef2).
(* prove fct2 *)
  rewrite (e ef1 (m ef2 (g o f))((m ef2 g)o(m ef2 f))).
  apply (f2 ef1).
  intro.
  unfold comp at 2.
  apply (f2 ef2).
Defined.

Corollary comppEFct (F G:k2): pEFct F -> pEFct G ->
      pEFct (fun X A => F X (G X A)).
Proof.
  red.
  intros.
  apply compEFct; auto.
Defined.

(** closure under sums *)
Lemma sumEFct (X Y:k1): EFct X -> EFct Y -> EFct (fun A => X A + Y A)%type.
Proof.
  intros ef1 ef2.
  set (m12:=fun (A B:Set)(f:A->B) x => match x with
    | inl y => inl _ (m ef1 f y)
    | inr y => inr _ (m ef2 f y)
  end).
  apply (mkEFct(m:=m12)); red; intros.
(* prove ext *)
  destruct r.
  simpl.
  apply (f_equal (fun x=>inl (A:=X B) (Y B) x)).
  apply (e ef1); trivial.
  simpl.
  apply (f_equal (fun x=>inr (X B) (B:=Y B) x)).
  apply (e ef2); trivial.
(* prove fct1 *)
  destruct x.
  simpl.
  apply (f_equal (fun x=>inl (A:=X A) (Y A) x)).
  apply (f1 ef1).
  simpl.
  apply (f_equal (fun x=>inr (X A) (B:=Y A) x)).
  apply (f1 ef2).
(* prove fct2 *)
  destruct x.
  simpl.
  rewrite (f2 ef1); reflexivity.
  simpl.
  rewrite (f2 ef2); reflexivity.
Defined.

Corollary sumpEFct (F G:k2): pEFct F -> pEFct G ->
      pEFct (fun X A => F X A + G X A)%type.
Proof.
  red.
  intros.
  apply sumEFct; auto.
Defined.

(** closure under products *)
Lemma prodEFct (X Y:k1): EFct X -> EFct Y -> EFct (fun A => X A * Y A)%type.
Proof.
  intros ef1 ef2.
  set (m12:=fun (A B:Set)(f:A->B) x => match x with
    (x1,x2) => (m ef1 f x1, m ef2 f x2) end).
  apply (mkEFct(m:=m12)); red; intros.
(* prove ext *)
  destruct r as [x1 x2].
  simpl.
  apply injective_projections; simpl.
  apply (e ef1); trivial.
  apply (e ef2); trivial.
(* prove fct1 *)
  destruct x as [x1 x2].
  simpl.
  apply injective_projections; simpl.
  apply (f1 ef1).
  apply (f1 ef2).
(* prove fct2 *)
  destruct x as [x1 x2].
  simpl.
  apply injective_projections; simpl.
  apply (f2 ef1).
  apply (f2 ef2).
Defined.

Corollary prodpEFct (F G:k2): pEFct F -> pEFct G ->
      pEFct (fun X A => F X A * G X A)%type.
Proof.
  red.
  intros.
  apply prodEFct; auto.
Defined.

(** the identity in k2 preserves extensional functors *)
Lemma idpEFct: pEFct (fun X => X).
Proof.
  red.
  intros.
  assumption.
Defined.

(** a variant for the eta-expanded identity *)
Lemma idpEFct_eta: pEFct (fun X A => X A).
Proof.
  red.
  intros X ef.
  destruct ef as [m0 e0 f01 f02].
  change (mon X) with (mon (fun A => X A)) in m0.
  apply (mkEFct (m:=m0) e0 f01 f02).
Defined.

(** the identity in k1 "is" an extensional functor *)
Lemma idEFct: EFct (fun A => A).
Proof.
  set (mId:=fun A B (f:A->B)(x:A) => f x).
  apply (mkEFct(m:=mId)).
  red.
  intros.
  unfold mId.
  apply H.
  red.
  reflexivity.
  red.
  reflexivity.
Defined.

(** constants in k2 *)
Lemma constpEFct (X:k1): EFct X  -> pEFct (fun _ => X).
Proof.
  red.
  intros.
  assumption.
Defined.

(** constants in k1 *)
Lemma constEFct (C:Set): EFct (fun _ => C).
Proof.
  set (mC:=fun A B (f:A->B)(x:C) => x).
  apply (mkEFct(m:=mC)); red; intros; unfold mC; reflexivity.
Defined.


(** the option type *)
Lemma optionEFct: EFct (fun (A:Set) => option A).
  apply (mkEFct (X:=fun (A:Set) => option A)(m:=option_map)); red; intros.
  destruct r.
  simpl.
  rewrite H.
  reflexivity.
  reflexivity.
  destruct x; reflexivity.
  destruct x; reflexivity.
Defined.


(** natural transformations from (X,mX) to (Y,mY) *)
Definition NAT(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y) : Prop :=
  forall (A B:Set)(f:A->B)(t:X A), j B (mX A B f t) = mY _ _ f (j A t).


Module Type LNMIt_Type.

Parameter F:k2.
Parameter FpEFct: pEFct F.
Parameter mu20: k1.
Definition  mu2: k1:= fun A => mu20 A.
Parameter mapmu2: mon mu2.
Definition MItType: Type :=
  forall G : k1, (forall X : k1, X c_k1 G -> F X c_k1 G) -> mu2 c_k1 G.
Parameter MIt0 : MItType.
Definition MIt : MItType:= fun G s A t => MIt0 s t.
Definition InType : Type :=
    forall (X:k1)(ef:EFct X)(j: X c_k1 mu2),
        NAT j (m ef) mapmu2 -> F X c_k1 mu2.
Parameter In : InType.
Axiom mapmu2Red : forall (A:Set)(X:k1)(ef:EFct X)(j: X c_k1 mu2)
    (n: NAT j (m ef) mapmu2)(t: F X A)(B:Set)(f:A->B),
            mapmu2 f (In ef n t) = In ef n (m (FpEFct ef) f t).
Axiom MItRed : forall (G : k1)
  (s : forall X : k1, X c_k1 G -> F X c_k1 G)(X : k1)(ef:EFct X)(j: X c_k1 mu2)
      (n: NAT j (m ef) mapmu2)(A:Set)(t:F X A),
     MIt s (In ef n t) = s X (fun A => (MIt s (A:=A)) o (j A)) A t.
Definition mu2IndType : Prop :=
  forall (P : (forall A : Set, mu2 A -> Prop)),
       (forall (X : k1)(ef:EFct X)(j : X c_k1 mu2)(n: NAT j (m ef) mapmu2),
          (forall (A : Set) (x : X A), P A (j A x)) ->
        forall (A:Set)(t : F X A), P A (In ef n t)) ->
    forall (A : Set) (r : mu2 A), P A r.
Axiom mu2Ind : mu2IndType.

End LNMIt_Type.

(** BushDepPredShort.v Version 0.2 July 2008 *)
(** does not need impredicative Set, produces stack overflow under V8.2, tested
with SVN 11296 *)

(** Copyright  Ralph Matthes, I.R.I.T.,  C.N.R.S. & University of Toulouse *)

Set Implicit Arguments.

Require Import List.

Definition listk1 (A:Set) : Set := list A.
Open Scope type_scope.

Definition BushF(X:k1)(A:Set) :=  unit + A  * X (X A).

Definition bushpEFct : pEFct BushF.
Proof.
  unfold BushF.
  apply sumpEFct.
  apply constpEFct.
  apply constEFct.
  apply prodpEFct.
  apply constpEFct.
  apply idEFct.
  apply comppEFct.
  apply idpEFct.
  apply idpEFct_eta.
Defined.

Module Type BUSH := LNMIt_Type with Definition F:=BushF
                                                with Definition FpEFct :=
bushpEFct.

Module Bush (BushBase:BUSH).

Definition Bush : k1 := BushBase.mu2.

Definition bush : mon Bush := BushBase.mapmu2.

End Bush.


Definition Id : k1 := fun X => X.

Fixpoint Pow (X:k1)(k:nat){struct k}:k1:=
  match k with 0 => Id
             |  S k' => fun A => X (Pow X k' A)
  end.

Fixpoint POW  (k:nat)(X:k1)(m:mon X){struct k} : mon (Pow X k) :=
  match k return mon (Pow X k)
      with 0 => fun _ _ f  => f
     |  S k' => fun _ _ f  => m _ _ (POW k' m f)
   end.

Module Type BushkToList_Type.

Declare Module Import BP: BUSH.
Definition F:=BushF.
Definition FpEFct:= bushpEFct.
Definition mu20 := mu20.
Definition mu2 := mu2.
Definition mapmu2 := mapmu2.
Definition MItType:= MItType.
Definition MIt0 := MIt0.
Definition MIt := MIt.
Definition InType := InType.
Definition In := In.
Definition mapmu2Red:=mapmu2Red.
Definition MItRed:=MItRed.
Definition mu2IndType:=mu2IndType.
Definition mu2Ind:=mu2Ind.

Definition  Bush:= mu2.
Module BushM := Bush BP.

Parameter BushkToList: forall(k:nat)(A:k0)(t:Pow Bush k A), list A.
Axiom BushkToList0: forall(A:k0)(t:Pow Bush 0 A), BushkToList 0 A t = t::nil.

End BushkToList_Type.

Module BushDep (BushkToListM:BushkToList_Type).

Module Bush := Bush BushkToListM.

Import Bush.
Import BushkToListM.


Lemma BushkToList0NAT: NAT(Y:=listk1) (BushkToList 0) (POW 0 bush) map.
Proof.
  red.
  intros.
  simpl.
  rewrite BushkToList0.
(* stack overflow for coqc and coqtop *)


Abort.
