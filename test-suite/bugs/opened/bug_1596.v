Require Import Relations.
Require Import FSets.
Require Import Arith.
Require Import Omega.

Set Keyed Unification.

Lemma Bool_elim_bool : forall (b:bool),b=true \/ b=false.
  destruct b;try tauto.
Qed.

Module OrderedPair (X:OrderedType) (Y:OrderedType) <: OrderedType with
Definition t := (X.t * Y.t)%type.
  Definition t := (X.t * Y.t)%type.

  Definition eq (xy1:t) (xy2:t) :=
    let (x1,y1) := xy1 in
      let (x2,y2) := xy2 in
        (X.eq x1 x2) /\ (Y.eq y1 y2).

  Definition lt (xy1:t) (xy2:t) :=
    let (x1,y1) := xy1 in
      let (x2,y2) := xy2 in
        (X.lt x1 x2) \/ ((X.eq x1 x2) /\ (Y.lt y1 y2)).

  Lemma eq_refl : forall (x:t),(eq x x).
    destruct x.
    unfold eq.
    split;[apply X.eq_refl | apply Y.eq_refl].
  Qed.

  Lemma eq_sym : forall (x y:t),(eq x y)->(eq y x).
    destruct x;destruct y;unfold eq;intro.
    elim H;clear H;intros.
    split;[apply X.eq_sym | apply Y.eq_sym];trivial.
  Qed.

  Lemma eq_trans : forall (x y z:t),(eq x y)->(eq y z)->(eq x z).
    unfold eq;destruct x;destruct y;destruct z;intros.
    elim H;clear H;intros.
    elim H0;clear H0;intros.
    split;[eapply X.eq_trans | eapply Y.eq_trans];eauto.
  Qed.

  Lemma lt_trans : forall (x y z:t),(lt x y)->(lt y z)->(lt x z).
    unfold lt;destruct x;destruct y;destruct z;intros.
    case H;clear H;intro.
    case H0;clear H0;intro.
    left.
    eapply X.lt_trans;eauto.
    elim H0;clear H0;intros.
    left.
    case (X.compare t0 t4);trivial;intros.
    generalize (X.eq_sym H0);intro.
    generalize (X.eq_trans e H2);intro.
    elim (X.lt_not_eq H H3).
    generalize (X.lt_trans l H);intro.
    generalize (X.eq_sym H0);intro.
    elim (X.lt_not_eq H2 H3).
    elim H;clear H;intros.
    case H0;clear H0;intro.
    left.
    case (X.compare t0 t4);trivial;intros.
    generalize (X.eq_sym H);intro.
    generalize (X.eq_trans H2 e);intro.
    elim (X.lt_not_eq H0 H3).
    generalize (X.lt_trans H0 l);intro.
    generalize (X.eq_sym H);intro.
    elim (X.lt_not_eq H2 H3).
    elim H0;clear H0;intros.
    right.
    split.
    eauto.
    eauto.
  Qed.

  Lemma lt_not_eq : forall (x y:t),(lt x y)->~(eq x y).
    unfold lt, eq;destruct x;destruct y;intro;intro.
    elim H0;clear H0;intros.
    case H.
    intro.
    apply (X.lt_not_eq H2 H0).
    intro.
    elim H2;clear H2;intros.
    apply (Y.lt_not_eq H3 H1).
  Qed.

  Definition compare : forall (x y:t),(Compare lt eq x y).
    destruct x;destruct y.
    case (X.compare t0 t2);intro.
    apply LT.
    left;trivial.
    case (Y.compare t1 t3);intro.
    apply LT.
    right.
    tauto.
    apply EQ.
    split;trivial.
    apply GT.
    right;auto.
    apply GT.
    left;trivial.
  Defined.

  Definition eq_dec : forall (x y: t), { eq x y } + { ~ eq x y}.
  Proof.
    intros [xa xb] [ya yb]; simpl.
    destruct (X.eq_dec xa ya).
    destruct (Y.eq_dec xb yb).
    + left; now split.
    + right. now intros [eqa eqb].
    + right. now intros [eqa eqb].
  Defined.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.
End OrderedPair.

Module MessageSpi.
  Inductive message : Set :=
  | MNam : nat -> message.

  Definition t := message.

  Fixpoint message_lt (m n:message) {struct m} : Prop :=
    match (m,n) with
      | (MNam n1,MNam n2) => n1 < n2
    end.

  Module Ord <: OrderedType with Definition t := message with Definition eq :=
@eq message.
    Definition t := message.
    Definition eq := @eq message.
    Definition lt := message_lt.

    Lemma eq_refl : forall (x:t),eq x x.
      unfold eq;auto.
    Qed.

    Lemma eq_sym : forall (x y:t),(eq x y )->(eq y x).
      unfold eq;auto.
    Qed.

    Lemma eq_trans : forall (x y z:t),(eq x y)->(eq y z)->(eq x z).
      unfold eq;auto;intros;congruence.
    Qed.

    Lemma lt_trans : forall (x y z:t),(lt x y)->(lt y z)->(lt x z).
      unfold lt.
      induction x;destruct y;simpl;try tauto;destruct z;try tauto;intros.
      omega.
    Qed.

    Lemma lt_not_eq : forall (x y:t),(lt x y)->~(eq x y).
      unfold eq;unfold lt.
      induction x;destruct y;simpl;try tauto;intro;red;intro;try (discriminate
H0);injection H0;intros.
      elim (lt_irrefl n);try omega.
    Qed.

    Definition compare : forall (x y:t),(Compare lt eq x y).
      unfold lt, eq.
      induction x;destruct y;intros;try (apply LT;simpl;trivial;fail);try
(apply
GT;simpl;trivial;fail).
      case (lt_eq_lt_dec n n0);intros;try (case s;clear s;intros).
      apply LT;trivial.
      apply EQ;trivial.
      rewrite e;trivial.
      apply GT;trivial.
    Defined.

    Definition eq_dec : forall (x y: t), { eq x y } + { ~ eq x y}.
    Proof.
    intros [i] [j]. unfold eq.
    destruct (eq_nat_dec i j).
    + left. now f_equal.
    + right. intros meq; now inversion meq.
    Defined.

    Hint Immediate eq_sym.
    Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.
  End Ord.

  Theorem eq_dec : forall (m n:message),{m=n}+{~(m=n)}.
    intros.
    case (Ord.compare m n);intro;[right | left | right];try (red;intro).
    elim (Ord.lt_not_eq m n);auto.
    rewrite e;auto.
    elim (Ord.lt_not_eq n m);auto.
  Defined.
End MessageSpi.

Module MessagePair := OrderedPair MessageSpi.Ord MessageSpi.Ord.

Module Type Hedge := FSetInterface.S with Module E := MessagePair.

Module A (H:Hedge).
  Definition hedge := H.t.

  Definition message_relation := relation MessageSpi.message.

  Definition relation_of_hedge (h:hedge) (m n:MessageSpi.message) := H.In (m,n)
h.

  Inductive hedge_synthesis_relation (h:message_relation) : message_relation :=
    | SynInc : forall (m n:MessageSpi.message),(h m
n)->(hedge_synthesis_relation h m n).

  Fixpoint hedge_in_synthesis (h:hedge) (m:MessageSpi.message)
(n:MessageSpi.message) {struct m} : bool :=
    if H.mem (m,n) h
      then true
      else false.

  Definition hedge_synthesis_spec (h:hedge) := hedge_synthesis_relation
(relation_of_hedge h).

  Lemma hedge_in_synthesis_impl_hedge_synthesis_spec : forall (h:hedge),forall
(m n:MessageSpi.message),(hedge_in_synthesis h m n)=true->(hedge_synthesis_spec
h m n).
    unfold hedge_synthesis_spec;unfold relation_of_hedge.
    induction m;simpl;intro.
    elim (Bool_elim_bool (H.mem (MessageSpi.MNam n,n0) h));intros.
    apply SynInc;apply H.mem_2;trivial.
    rewrite H in H0.  (* !! possible here !! *)
    discriminate H0.
  Qed.
End A.

Module B (H:Hedge).
  Definition hedge := H.t.

  Definition message_relation := relation MessageSpi.t.

  Definition relation_of_hedge (h:hedge) (m n:MessageSpi.t) := H.In (m,n) h.

  Inductive hedge_synthesis_relation (h:message_relation) : message_relation :=
    | SynInc : forall (m n:MessageSpi.t),(h m n)->(hedge_synthesis_relation h m
n).

  Fixpoint hedge_in_synthesis (h:hedge) (m:MessageSpi.t) (n:MessageSpi.t)
{struct m} : bool :=
    if H.mem (m,n) h
      then true
      else false.

  Definition hedge_synthesis_spec (h:hedge) := hedge_synthesis_relation
(relation_of_hedge h).

  Lemma hedge_in_synthesis_impl_hedge_synthesis_spec : forall (h:hedge),forall
(m n:MessageSpi.t),(hedge_in_synthesis h m n)=true->(hedge_synthesis_spec h m
n).
    unfold hedge_synthesis_spec;unfold relation_of_hedge.
    induction m;simpl;intro.
    elim (Bool_elim_bool (H.mem (MessageSpi.MNam n,n0) h));intros.
    apply SynInc;apply H.mem_2;trivial.
    rewrite H in H0. discriminate. (* !! impossible here !! *)
  Qed.
End B.
