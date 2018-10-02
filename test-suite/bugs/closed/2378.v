Require Import TestSuite.admit.
(* test with Coq 8.3rc1 *)

Require Import Program.

Inductive Unit: Set := unit: Unit.

Definition eq_dec T := forall x y:T, {x=y}+{x<>y}.

Section TTS_TASM.

Variable Time: Set.
Variable Zero: Time.
Variable tle: Time -> Time -> Prop.
Variable tlt: Time -> Time -> Prop.
Variable tadd: Time -> Time -> Time.
Variable tsub: Time -> Time -> Time.
Variable tmin: Time -> Time -> Time.
Notation "t1 @<= t2" := (tle t1 t2) (at level 70, no associativity).
Notation "t1 @< t2" := (tlt t1 t2) (at level 70, no associativity).
Notation "t1 @+ t2" := (tadd t1 t2) (at level 50, left associativity).
Notation "t1 @- t2" := (tsub t1 t2) (at level 50, left associativity).
Notation "t1 @<= t2 @<= t3" := ((tle t1 t2) /\ (tle t2 t3)) (at level 70, t2 at next level).
Notation "t1 @<= t2 @< t3" := ((tle t1 t2) /\ (tlt t2 t3)) (at level 70, t2 at next level).

Variable tzerop: forall n, (n = Zero) + {Zero @< n}.
Variable tlt_eq_gt_dec: forall x y, {x @< y} + {x=y} + {y @< x}.
Variable tle_plus_l: forall n m, n @<= n @+ m.
Variable tle_lt_eq_dec: forall n m, n @<= m -> {n @< m} + {n = m}.

Variable tzerop_zero: tzerop Zero = inleft (Zero @< Zero) (@eq_refl _ Zero).
Variable tplus_n_O: forall n, n @+ Zero = n.
Variable tlt_le_weak: forall n m, n @< m -> n @<= m.
Variable tlt_irrefl: forall n, ~ n @< n.
Variable tplus_nlt: forall n m, ~n @+ m @< n.
Variable tle_n: forall n, n @<= n.
Variable tplus_lt_compat_l: forall n m p, n @< m -> p @+ n @< p @+ m.
Variable tlt_trans: forall n m p, n @< m -> m @< p -> n @< p.
Variable tle_lt_trans: forall n m p, n @<= m -> m @< p -> n @< p.
Variable tlt_le_trans: forall n m p, n @< m -> m @<= p -> n @< p.
Variable tle_refl: forall n, n @<= n.
Variable tplus_le_0: forall n m, n @+ m @<= n -> m = Zero.
Variable Time_eq_dec: eq_dec Time.

(*************************************************************)

Section PropLogic.
Variable Predicate: Type.

Inductive LP: Type :=
  LPPred: Predicate -> LP
| LPAnd: LP -> LP -> LP
| LPNot: LP -> LP.

Variable State: Type.
Variable Sat: State -> Predicate -> Prop.

Fixpoint lpSat st f: Prop :=
  match f with
    LPPred p => Sat st p
  | LPAnd f1 f2 => lpSat st f1 /\ lpSat st f2
  | LPNot f1 => ~lpSat st f1
  end.
End PropLogic.

Arguments lpSat : default implicits.

Fixpoint LPTransfo Pred1 Pred2 p2lp (f: LP Pred1): LP Pred2 :=
  match f with
    LPPred _ p => p2lp p
  | LPAnd _ f1 f2 => LPAnd _ (LPTransfo Pred1 Pred2 p2lp f1) (LPTransfo Pred1 Pred2 p2lp f2)
  | LPNot _ f1 => LPNot _ (LPTransfo Pred1 Pred2 p2lp f1)
  end.
Arguments LPTransfo : default implicits.

Definition addIndex (Ind:Type) (Pred: Ind -> Type) (i: Ind) f :=
  LPTransfo (fun p => LPPred _ (existT (fun i => Pred i) i p)) f.

Section TTS.

Variable State: Type.

Record TTS: Type := mkTTS {
  Init: State -> Prop;
  Delay: State -> Time -> State -> Prop;
  Next: State -> State -> Prop;
  Predicate: Type;
  Satisfy: State -> Predicate -> Prop
}.

Definition TTSIndexedProduct Ind (tts: Ind -> TTS): TTS := mkTTS
  (fun st => forall i, Init (tts i) st)
  (fun st d st' => forall i, Delay (tts i) st d st')
  (fun st st' => forall i, Next (tts i) st st')
  { i: Ind & Predicate (tts i) }
  (fun st p => Satisfy (tts (projT1 p)) st (projT2 p)).

End TTS.

Section SIMU_F.

Variables StateA StateC: Type.

Record mapping: Type := mkMapping {
  mState: Type;
  mInit: StateC -> mState;
  mNext: mState -> StateC -> mState;
  mDelay: mState -> StateC -> Time -> mState;
  mabs: mState -> StateC -> StateA
}.

Variable m: mapping.

Record simu (Pred: Type) (a: TTS StateA) (c: TTS StateC) (tra: Pred -> LP (Predicate _ a)) (trc: Pred -> LP (Predicate _ c)): Type := simuPrf {
  inv: (mState m) -> StateC -> Prop;
  invInit: forall st, Init _ c st -> inv (mInit m st) st;
  invDelay: forall ex1 st1 st2 d, Delay _ c st1 d st2 -> inv ex1 st1 -> inv (mDelay m ex1 st1 d) st2;
  invNext: forall ex1 st1 st2, Next _ c st1 st2 -> inv ex1 st1 -> inv (mNext m ex1 st1) st2;
  simuInit: forall st, Init _ c st -> Init _ a (mabs m (mInit m st) st);
  simuDelay: forall ex1 st1 st2 d, Delay _ c st1 d st2 -> inv ex1 st1 ->
    Delay _ a (mabs m ex1 st1) d (mabs m (mDelay m ex1 st1 d) st2);
  simuNext: forall ex1 st1 st2, Next _ c st1 st2 -> inv ex1 st1 ->
    Next _ a (mabs m ex1 st1) (mabs m (mNext m ex1 st1) st2);
  simuPred: forall ext st, inv ext st ->
    (forall p, lpSat (Satisfy _ c) st (trc p) <-> lpSat (Satisfy _ a) (mabs m ext st) (tra p))
}.

Theorem satProd: forall State Ind Pred (Sat: forall i, State -> Pred i -> Prop) (st:State) i (f: LP (Pred i)),
  lpSat (Sat i) st f
  <->
  lpSat
    (fun (st : State) (p : {i : Ind &  Pred i}) => Sat (projT1 p) st (projT2 p)) st
     (addIndex Ind _ i f).
Proof.
  induction f; simpl; intros; split; intros; intuition.
Qed.

Definition trProd (State: Type) Ind (Pred: Ind -> Type) (tts: Ind -> TTS State) (tr: forall i, (Pred i) -> LP (Predicate _ (tts i))):
  {i:Ind & Pred i} -> LP (Predicate _ (TTSIndexedProduct _ Ind tts)) :=
  fun p => addIndex Ind _ (projT1 p) (tr (projT1 p) (projT2 p)).

Arguments trProd : default implicits.
Require Import Setoid.

Theorem satTrProd:
  forall State Ind Pred (tts: Ind -> TTS State)
    (tr: forall i, (Pred  i) -> LP (Predicate _ (tts i))) (st:State) (p: {i:Ind & (Pred i)}),
  lpSat (Satisfy _ (tts (projT1 p))) st (tr (projT1 p) (projT2 p))
  <->
  lpSat (Satisfy _ (TTSIndexedProduct _ _ tts)) st (trProd _ tts tr p).
Proof.
  unfold trProd, TTSIndexedProduct; simpl; intros.
  rewrite (satProd State Ind (fun i => Predicate State (tts i))
                      (fun i => Satisfy _ (tts i))); tauto.
Qed.

Theorem simuProd:
  forall Ind (Pred: Ind -> Type) (tta: Ind -> TTS StateA) (ttc: Ind -> TTS StateC)
    (tra: forall i, (Pred i) -> LP (Predicate _ (tta i)))
    (trc: forall i, (Pred i) -> LP (Predicate _ (ttc i))),
     (forall i, simu _ (tta i) (ttc i) (tra i) (trc i)) ->
       simu _ (TTSIndexedProduct _ Ind tta) (TTSIndexedProduct _ Ind ttc)
                  (trProd Pred tta tra) (trProd Pred ttc trc).
Proof.
  intros.
  apply simuPrf with (fun ex st => forall i, inv _ _ (ttc i) (tra i) (trc i) (X i) ex st); simpl; intros; auto.
  eapply invInit; eauto.
  eapply invDelay; eauto.
  eapply invNext; eauto.
  eapply simuInit; eauto.
  eapply simuDelay; eauto.
  eapply simuNext; eauto.
  split; simpl; intros.
  generalize (proj1 (simuPred _ _ _ _ _ (X (projT1 p)) ext st (H (projT1 p)) (projT2 p))); simpl; intro.
  rewrite <- (satTrProd StateA Ind Pred tta tra); apply H1.
  rewrite (satTrProd StateC Ind Pred ttc trc); apply H0.

  generalize (proj2 (simuPred _ _ _ _ _ (X (projT1 p)) ext st (H (projT1 p)) (projT2 p))); simpl; intro.
  rewrite <- (satTrProd StateC Ind Pred ttc trc); apply H1.
  rewrite (satTrProd StateA Ind Pred tta tra); apply H0.
Qed.

End SIMU_F.

Section TRANSFO.

Record simu_equiv StateA StateC m1 m2 Pred (a: TTS StateA) (c: TTS StateC) (tra: Pred -> LP (Predicate _ a)) (trc: Pred -> LP (Predicate _ c)): Type := simuEquivPrf {
  simuLR: simu StateA StateC m1 Pred a c tra trc;
  simuRL: simu StateC StateA m2 Pred c a trc tra
}.

Theorem simu_equivProd:
  forall StateA StateC m1 m2 Ind (Pred: Ind -> Type) (tta: Ind -> TTS StateA) (ttc: Ind -> TTS StateC)
    (tra: forall i, (Pred i) -> LP (Predicate _ (tta i)))
    (trc: forall i, (Pred i) -> LP (Predicate _ (ttc i))),
     (forall i, simu_equiv StateA StateC m1 m2 _ (tta i) (ttc i) (tra i) (trc i)) ->
       simu_equiv StateA StateC m1 m2 _ (TTSIndexedProduct _ Ind tta) (TTSIndexedProduct _ Ind ttc)
                  (trProd _ _ Pred tta tra) (trProd _ _ Pred ttc trc).
Proof.
  intros; split; intros.
  apply simuProd; intro.
  elim (X i); auto.
  apply simuProd; intro.
  elim (X i); auto.
Qed.

Record RTLanguage: Type := mkRTLanguage {
   Syntax: Type;
   DynamicState: Syntax -> Type;
   Semantic: forall (mdl:Syntax), TTS (DynamicState mdl);
   MdlPredicate: Syntax -> Type;
   MdlPredicateDefinition: forall mdl, MdlPredicate mdl -> LP (Predicate _ (Semantic mdl))
}.

Record Transformation (l1 l2: RTLanguage): Type := mkTransformation {
  Tmodel: Syntax l1 -> Syntax l2;
  Tl1l2: forall mdl, mapping (DynamicState l1 mdl) (DynamicState l2 (Tmodel mdl));
  Tl2l1: forall mdl, mapping (DynamicState l2 (Tmodel mdl)) (DynamicState l1 mdl);
  Tpred: forall mdl, MdlPredicate l1 mdl -> LP (MdlPredicate l2 (Tmodel mdl));
  Tsim: forall mdl, simu_equiv (DynamicState l1 mdl) (DynamicState l2 (Tmodel mdl)) (Tl1l2 mdl) (Tl2l1 mdl)
    (MdlPredicate l1 mdl) (Semantic l1 mdl) (Semantic l2 (Tmodel mdl))
    (MdlPredicateDefinition l1 mdl)
    (fun p => LPTransfo (MdlPredicateDefinition l2 (Tmodel mdl)) (Tpred mdl p))
}.

Section Product.

Record PSyntax (L: RTLanguage): Type := mkPSyntax {
  pIndex: Type;
  pIsEmpty: pIndex + {pIndex -> False};
  pState: Type;
  pComponents: pIndex -> Syntax L;
  pIsShared: forall i, DynamicState L (pComponents i) = pState
}.

Definition pPredicate (L: RTLanguage) (sys: PSyntax L) := { i : pIndex L sys & MdlPredicate L (pComponents L sys i)}.

(* product with shared state *)

Definition PLanguage (L: RTLanguage): RTLanguage :=
  mkRTLanguage
    (PSyntax L)
    (pState L)
    (fun mdl => TTSIndexedProduct (pState L mdl) (pIndex L mdl)
      (fun i => match pIsShared L mdl i in (_ = y) return TTS y with
        eq_refl => Semantic L (pComponents L mdl i)
       end))
    (pPredicate L)
    (fun mdl => trProd _ _ _ _
      (fun i pi => match pIsShared L mdl i as e in (_ = y) return
                     (LP (Predicate y
                               match e in (_ = y0) return (TTS y0) with
                               | eq_refl => Semantic L (pComponents L mdl i)
                               end))
     with
     | eq_refl => MdlPredicateDefinition L (pComponents L mdl i) pi
     end)).

Inductive Empty: Type :=.

Record isSharedTransfo l1 l2 tr: Prop := isSharedTransfoPrf {
sameState:  forall mdl i j,
  DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i)) =
  DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl j));
sameMState: forall mdl i j,
  mState _ _  (Tl1l2 _ _ tr (pComponents l1 mdl i)) =
  mState _ _  (Tl1l2 _ _ tr (pComponents l1 mdl j));
sameM12: forall mdl i j,
  Tl1l2 _ _ tr (pComponents l1 mdl i) =
  match sym_eq (sameState mdl i j) in _=y return mapping _ y with
    eq_refl => match sym_eq (pIsShared l1 mdl i) in _=x return mapping x _ with
      eq_refl => match pIsShared l1 mdl j in _=x return mapping x _ with
        eq_refl => Tl1l2 _ _ tr (pComponents l1 mdl j)
      end
    end
  end;
sameM21: forall mdl i j,
  Tl2l1 l1 l2 tr (pComponents l1 mdl i) =
  match
    sym_eq (sameState mdl i j) in (_ = y)
    return (mapping y (DynamicState l1 (pComponents l1 mdl i)))
  with eq_refl =>
    match
      sym_eq (pIsShared l1 mdl i) in (_ = y)
      return
        (mapping (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl j))) y)
    with
    | eq_refl =>
        match
          pIsShared l1 mdl j in (_ = y)
          return
            (mapping
               (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl j))) y)
        with
        | eq_refl => Tl2l1 l1 l2 tr (pComponents l1 mdl j)
        end
    end
end
}.

Definition PTransfoSyntax l1 l2 tr (h: isSharedTransfo l1 l2 tr) mdl :=
  mkPSyntax l2 (pIndex l1 mdl)
    (pIsEmpty l1 mdl)
    (match pIsEmpty l1 mdl return Type with
         inleft i => DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i))
        |inright h => pState l1 mdl
       end)
    (fun i => Tmodel l1 l2 tr (pComponents l1 mdl i))
    (fun i => match pIsEmpty l1 mdl as y return
        (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i)) =
         match y with
         | inleft i0 =>
             DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i0))
         | inright _ => pState l1 mdl
         end)
      with
         inleft j => sameState l1 l2 tr h mdl i j
      | inright h => match h i with end
        end).

Definition compSemantic l mdl i :=
    match pIsShared l mdl i in (_=y) return TTS y with
        eq_refl => Semantic l (pComponents l mdl i)
    end.

Definition compSemanticEq l mdl i s (e: DynamicState l (pComponents l mdl i) = s) :=
    match e in (_=y) return TTS y with
        eq_refl => Semantic l (pComponents l mdl i)
    end.

Definition Pmap12 l1 l2 tr (h: isSharedTransfo l1 l2 tr) (mdl : PSyntax l1) :=
match
  pIsEmpty l1 mdl as s
  return
    (mapping (pState l1 mdl)
       match s with
       | inleft i => DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i))
       | inright _ => pState l1 mdl
       end)
with
| inleft p =>
    match
      pIsShared l1 mdl p in (_ = y)
      return
        (mapping y (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl p))))
    with
    | eq_refl => Tl1l2 l1 l2 tr (pComponents l1 mdl p)
    end
| inright _ =>
    mkMapping (pState l1 mdl) (pState l1 mdl) Unit
      (fun _ : pState l1 mdl => unit)
      (fun (_ : Unit) (_ : pState l1 mdl) => unit)
      (fun (_ : Unit) (_ : pState l1 mdl) (_ : Time) => unit)
      (fun (_ : Unit) (X : pState l1 mdl) => X)
end.

Definition Pmap21 l1 l2 tr (h : isSharedTransfo l1 l2 tr) mdl :=
match
  pIsEmpty l1 mdl as s
  return
    (mapping
       match s with
       | inleft i => DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i))
       | inright _ => pState l1 mdl
       end (pState l1 mdl))
with
| inleft p =>
    match
      pIsShared l1 mdl p in (_ = y)
      return
        (mapping (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl p))) y)
    with
    | eq_refl => Tl2l1 l1 l2 tr (pComponents l1 mdl p)
    end
| inright _ =>
    mkMapping (pState l1 mdl) (pState l1 mdl) Unit
      (fun _ : pState l1 mdl => unit)
      (fun (_ : Unit) (_ : pState l1 mdl) => unit)
      (fun (_ : Unit) (_ : pState l1 mdl) (_ : Time) => unit)
      (fun (_ : Unit) (X : pState l1 mdl) => X)
end.

Definition PTpred l1 l2 tr (h : isSharedTransfo l1 l2 tr) mdl (pp : pPredicate l1 mdl):
  LP (MdlPredicate (PLanguage l2) (PTransfoSyntax l1 l2 tr h mdl)) :=
match pIsEmpty l1 mdl with
| inleft _ =>
      let (x, p) := pp in
      addIndex (pIndex l1 mdl) (fun i => MdlPredicate l2 (Tmodel l1 l2 tr (pComponents l1 mdl i))) x
        (LPTransfo (Tpred l1 l2 tr (pComponents l1 mdl x))
          (LPPred (MdlPredicate l1 (pComponents l1 mdl x)) p))
| inright f => match f (projT1 pp) with end
end.

Lemma simu_eqA:
  forall A1 A2 C m P sa sc tta ttc (h: A2=A1),
  simu A1 C (match h in (_=y) return mapping _ C with eq_refl => m end)
  P (match h in (_=y) return TTS y with eq_refl => sa end)
  sc (fun p => match h in (_=y) return LP (Predicate y _) with eq_refl => tta p end)
  ttc ->
  simu A2 C m P sa sc tta ttc.
admit.
Qed.

Lemma simu_eqC:
  forall A C1 C2 m P sa sc tta ttc (h: C2=C1),
  simu A C1 (match h in (_=y) return mapping A _ with eq_refl => m end)
  P sa (match h in (_=y) return TTS y with eq_refl => sc end)
  tta (fun p => match h in (_=y) return LP (Predicate y _) with eq_refl => ttc p end)
   ->
  simu A C2 m P sa sc tta ttc.
admit.
Qed.

Lemma simu_eqA1:
  forall A1 A2 C m P sa sc tta ttc (h: A1=A2),
  simu A1 C m
  P
  (match (sym_eq h) in (_=y) return TTS y with eq_refl => sa end) sc
  (fun p => match (sym_eq h) as e in (_=y) return LP (Predicate y (match e in (_=z) return TTS z with eq_refl => sa end)) with eq_refl => tta p end) ttc
   ->
  simu A2 C (match h in (_=y) return mapping _ C with eq_refl => m end) P sa sc tta ttc.
admit.
Qed.

Lemma simu_eqA2:
  forall A1 A2 C m P sa sc tta ttc (h: A1=A2),
  simu A1 C (match (sym_eq h) in (_=y) return mapping _ C with eq_refl => m end)
  P
  sa sc tta ttc
   ->
  simu A2 C m P
  (match h in (_=y) return TTS y with eq_refl => sa end) sc
  (fun p => match h as e in (_=y) return LP (Predicate y match e in (_=y0) return TTS y0 with eq_refl => sa end) with eq_refl => tta p end)
 ttc.
admit.
Qed.

Lemma simu_eqC2:
  forall A C1 C2 m P sa sc tta ttc (h: C1=C2),
  simu A C1 (match (sym_eq h) in (_=y) return mapping A _ with eq_refl => m end)
  P
  sa sc tta ttc
   ->
  simu A C2 m P
  sa (match h in (_=y) return TTS y with eq_refl => sc end)
  tta (fun p => match h as e in (_=y) return LP (Predicate y match e in (_=y0) return TTS y0 with eq_refl => sc end) with eq_refl => ttc p end).
admit.
Qed.

Lemma simu_eqM:
  forall A C m1 m2 P sa sc tta ttc (h: m1=m2),
  simu A C m1 P sa sc tta ttc
   ->
  simu A C m2 P sa sc tta ttc.
admit.
Qed.

Lemma LPTransfo_trans:
  forall Pred1 Pred2 Pred3 (tr1: Pred1 -> LP Pred2) (tr2: Pred2 -> LP Pred3) f,
    LPTransfo tr2 (LPTransfo tr1 f) = LPTransfo (fun x => LPTransfo tr2 (tr1 x)) f.
Proof.
  admit.
Qed.

Lemma LPTransfo_addIndex:
  forall Ind Pred tr1 x (tr2: forall i, Pred i -> LP (tr1 i)) (p: LP (Pred x)),
    addIndex Ind tr1 x (LPTransfo (tr2 x) p) =
    LPTransfo
      (fun p0 : {i : Ind & Pred i} =>
        addIndex Ind tr1 (projT1 p0) (tr2 (projT1 p0) (projT2 p0)))
      (addIndex Ind Pred x p).
Proof.
  unfold addIndex; intros.
  rewrite LPTransfo_trans.
  rewrite LPTransfo_trans.
  simpl.
  auto.
Qed.

Record tr_compat I0 I1 tr := compatPrf {
  and_compat: forall p1 p2, tr (LPAnd I0 p1 p2) = LPAnd I1 (tr p1) (tr p2);
  not_compat: forall p, tr (LPNot I0 p) = LPNot I1 (tr p)
}.

Lemma LPTransfo_addIndex_tr:
  forall Ind Pred tr0 tr1 x (tr2: forall i, Pred i -> LP (tr0 i))  (tr3: forall i, LP (tr0 i) -> LP (tr1 i)) (p: LP (Pred x)),
    (forall x, tr_compat (tr0 x) (tr1 x) (tr3 x)) ->
    addIndex Ind tr1 x (tr3 x (LPTransfo (tr2 x) p)) =
    LPTransfo
      (fun p0 : {i : Ind & Pred i} =>
        addIndex Ind tr1 (projT1 p0) (tr3 (projT1 p0) (tr2 (projT1 p0) (projT2 p0))))
      (addIndex Ind Pred x p).
Proof.
  unfold addIndex; simpl; intros.
  rewrite LPTransfo_trans; simpl.
  rewrite <- LPTransfo_trans.
  f_equal.
  induction p; simpl; intros; auto.
  rewrite (and_compat _ _ _ (H x)).
  rewrite <- IHp1, <- IHp2; auto.
  rewrite <- IHp.
  rewrite (not_compat _ _ _ (H x)); auto.
Qed.

Require Export Coq.Logic.FunctionalExtensionality.
Print PLanguage.

Program Definition PTransfo l1 l2 (tr: Transformation l1 l2) (h: isSharedTransfo l1 l2 tr):
Transformation (PLanguage l1) (PLanguage l2) :=
  mkTransformation (PLanguage l1) (PLanguage l2)
    (PTransfoSyntax l1 l2 tr h)
    (Pmap12 l1 l2 tr h)
    (Pmap21 l1 l2 tr h)
    (PTpred l1 l2 tr h)
    (fun mdl => simu_equivProd
      (pState l1 mdl)
      (pState l2 (PTransfoSyntax l1 l2 tr h mdl))
      (Pmap12 l1 l2 tr h mdl)
      (Pmap21 l1 l2 tr h mdl)
      (pIndex l1 mdl)
      (fun i => MdlPredicate l1 (pComponents l1 mdl i))
      (compSemantic l1 mdl)
      (compSemantic l2 (PTransfoSyntax l1 l2 tr h mdl))
      _
      _
      _
        ).

Next Obligation.
  unfold compSemantic, PTransfoSyntax; simpl.
  case (pIsEmpty l1 mdl); simpl; intros.
  unfold pPredicate; simpl.
  unfold pPredicate in X; simpl in X.
  case (sameState l1 l2 tr h mdl i p).
  apply (LPTransfo (MdlPredicateDefinition l2 (Tmodel l1 l2 tr (pComponents l1 mdl i)))).
  apply (LPTransfo (Tpred l1 l2 tr (pComponents l1 mdl i))).
  apply (LPPred _ X).

  apply False_rect; apply (f i).
Defined.

Next Obligation.
  split; intros.
  unfold Pmap12; simpl.
  unfold PTransfo_obligation_1; simpl.
  unfold compSemantic; simpl.
  unfold eq_ind, eq_rect, f_equal; simpl.
  case (pIsEmpty l1 mdl); intros.
  apply simu_eqA2.
  apply simu_eqC2.
  apply simu_eqM with (Tl1l2 l1 l2 tr (pComponents l1 mdl i)).
  apply sameM12.
  apply (simuLR _ _ _ _ _ _ _ _ _ (Tsim l1 l2 tr (pComponents l1 mdl i))); intro.

  apply False_rect; apply (f i).

  unfold Pmap21; simpl.
  unfold PTransfo_obligation_1; simpl.
  unfold compSemantic; simpl.
  unfold eq_ind, eq_rect, f_equal; simpl.
  case (pIsEmpty l1 mdl); intros.
  apply simu_eqC2.
  apply simu_eqA2.
  apply simu_eqM with (Tl2l1 l1 l2 tr (pComponents l1 mdl i)).
  apply sameM21.
  apply (simuRL _ _ _ _ _ _ _ _ _ (Tsim l1 l2 tr (pComponents l1 mdl i))); intro.

  apply False_rect; apply (f i).
Qed.

Next Obligation.
  unfold trProd; simpl.
  unfold PTransfo_obligation_1; simpl.
  unfold compSemantic; simpl.
  unfold eq_ind, eq_rect, f_equal; simpl.
  apply functional_extensionality; intro.
  case x; clear x; intros.
  unfold PTpred; simpl.
  case (pIsEmpty l1 mdl); simpl; intros.
  set (tr0 i :=
   Predicate (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl i)))
     (Semantic l2 (Tmodel l1 l2 tr (pComponents l1 mdl i)))).
  set (tr1 i :=
   Predicate (DynamicState l2 (Tmodel l1 l2 tr (pComponents l1 mdl p)))
     match sameState l1 l2 tr h mdl i p in (_ = y) return (TTS y) with
     | eq_refl => Semantic l2 (Tmodel l1 l2 tr (pComponents l1 mdl i))
     end).
  set (tr2 x := MdlPredicateDefinition l2 (Tmodel l1 l2 tr (pComponents l1 mdl x))).
  set (Pred x := MdlPredicate l2 (Tmodel l1 l2 tr (pComponents l1 mdl x))).
  set (tr3 x f := match
    sameState l1 l2 tr h mdl x p as e in (_ = y)
    return
      (LP
         (Predicate y
            match e in (_ = y0) return (TTS y0) with
            | eq_refl => Semantic l2 (Tmodel l1 l2 tr (pComponents l1 mdl x))
            end))
  with
  | eq_refl => f
  end).
  apply (LPTransfo_addIndex_tr _ Pred tr0 tr1 x tr2 tr3
    (Tpred l1 l2 tr (pComponents l1 mdl x) m)).
  unfold tr0, tr1, tr3; intros; split; simpl; intros; auto.
  case (sameState l1 l2 tr h mdl x0 p); auto.
  case (sameState l1 l2 tr h mdl x0 p); auto.

  apply False_rect; apply (f x).
Qed.

End Product.
