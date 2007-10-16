Require Import Ring_polynom.


Require Import NArith.
Require Import Relation_Definitions.
Require Import Setoid.
Require Import Ring_polynom.
Require Import List.
Require Import Bool.
Require Import OrderedRing.
Require Import Refl.
Require Import CheckerMaker.

Set Implicit Arguments.

Import OrderedRingSyntax.

Section Micromega.

(* Assume we have a strict(ly?) ordered ring *)

Variable R : Type.
Variables rO rI : R.
Variables rplus rtimes rminus: R -> R -> R.
Variable ropp : R -> R.
Variables req rle rlt : R -> R -> Prop.

Variable sor : SOR rO rI rplus rtimes rminus ropp req rle rlt.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (rplus x y).
Notation "x * y " := (rtimes x y).
Notation "x - y " := (rminus x y).
Notation "- x" := (ropp x).
Notation "x == y" := (req x y).
Notation "x ~= y" := (~ req x y).
Notation "x <= y" := (rle x y).
Notation "x < y" := (rlt x y).

(* Assume we have a type of coefficients C and a morphism from C to R *)

Variable C : Type.
Variables cO cI : C.
Variables cplus ctimes cminus: C -> C -> C.
Variable copp : C -> C.
Variables ceqb cleb : C -> C -> bool.
Variable phi : C -> R.

(* Power coefficients *)
Variable E : Set. (* the type of exponents *)
Variable pow_phi : N -> E.
Variable rpow : R -> E -> R.

Notation "[ x ]" := (phi x).
Notation "x [=] y" := (ceqb x y).
Notation "x [<=] y" := (cleb x y).

(* Let's collect all hypotheses in addition to the ordered ring axioms into
one structure *)

Record SORaddon := mk_SOR_addon {
  SORrm : ring_morph 0 1 rplus rtimes rminus ropp req cO cI cplus ctimes cminus copp ceqb phi;
  SORpower : power_theory rI rtimes req pow_phi rpow;
  SORcneqb_morph : forall x y : C, x [=] y = false -> [x] ~= [y];
  SORcleb_morph : forall x y : C, x [<=] y = true -> [x] <= [y]
}.

Variable addon : SORaddon.

Add Relation R req
  reflexivity proved by sor.(SORsetoid).(Seq_refl _ _)
  symmetry proved by sor.(SORsetoid).(Seq_sym _ _)
  transitivity proved by sor.(SORsetoid).(Seq_trans _ _)
as micomega_sor_setoid.

Add Morphism rplus with signature req ==> req ==> req as rplus_morph.
Proof.
exact sor.(SORplus_wd).
Qed.
Add Morphism rtimes with signature req ==> req ==> req as rtimes_morph.
Proof.
exact sor.(SORtimes_wd).
Qed.
Add Morphism ropp with signature req ==> req as ropp_morph.
Proof.
exact sor.(SORopp_wd).
Qed.
Add Morphism rle with signature req ==> req ==> iff as rle_morph.
Proof.
exact sor.(SORle_wd).
Qed.
Add Morphism rlt with signature req ==> req ==> iff as rlt_morph.
Proof.
exact sor.(SORlt_wd).
Qed.

Add Morphism rminus with signature req ==> req ==> req as rminus_morph.
Proof (rminus_morph sor). (* We already proved that minus is a morphism in OrderedRing.v *)

Definition cneqb (x y : C) := negb (ceqb x y).
Definition cltb (x y : C) := (cleb x y) && (cneqb x y).

Notation "x [~=] y" := (cneqb x y).
Notation "x [<] y" := (cltb x y).

Ltac le_less := rewrite (Rle_lt_eq sor); left; try assumption.
Ltac le_equal := rewrite (Rle_lt_eq sor); right; try reflexivity; try assumption.
Ltac le_elim H := rewrite (Rle_lt_eq sor) in H; destruct H as [H | H].

Lemma cleb_sound : forall x y : C, x [<=] y = true -> [x] <= [y].
Proof addon.(SORcleb_morph).

Lemma cneqb_sound : forall x y : C, x [~=] y = true -> [x] ~= [y].
Proof.
intros x y H1. apply addon.(SORcneqb_morph). unfold cneqb, negb in H1.
destruct (ceqb x y); now try discriminate.
Qed.

Lemma cltb_sound : forall x y : C, x [<] y = true -> [x] < [y].
Proof.
intros x y H. unfold cltb in H. apply andb_prop in H. destruct H as [H1 H2].
apply cleb_sound in H1. apply cneqb_sound in H2. apply <- (Rlt_le_neq sor). now split.
Qed.

(* Begin Micromega *)

Definition PExprC := PExpr C. (* arbitrary expressions built from +, *, - *)
Definition PolC := Pol C. (* polynomials in generalized Horner form, defined in Ring_polynom *)
Definition Env := list R.

Definition eval_pexpr : Env -> PExprC -> R := PEeval 0 rplus rtimes rminus ropp phi pow_phi rpow.
Definition eval_pol : Env -> PolC -> R := Pphi 0 rplus rtimes phi.

Inductive Op2 : Set := (* binary relations *)
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt.

Definition eval_op2 (o : Op2) : R -> R -> Prop :=
match o with
| OpEq => req
| OpNEq => fun x y : R => x ~= y
| OpLe => rle
| OpGe => fun x y : R => y <= x
| OpLt => fun x y : R => x < y
| OpGt => fun x y : R => y < x
end.

Record Formula : Type := {
  Flhs : PExprC;
  Fop : Op2;
  Frhs : PExprC
}.

Definition eval_formula (env : Env) (f : Formula) : Prop :=
  let (lhs, op, rhs) := f in
    (eval_op2 op) (eval_pexpr env lhs) (eval_pexpr env rhs).

(* We normalize Formulas by moving terms to one side *)

Inductive Op1 : Set := (* relations with 0 *)
| Equal (* == 0 *)
| NonEqual (* ~= 0 *)
| Strict (* > 0 *)
| NonStrict (* >= 0 *).

Definition NFormula := (PExprC * Op1)%type. (* normalized formula *)

Definition eval_op1 (o : Op1) : R -> Prop :=
match o with
| Equal => fun x => x == 0
| NonEqual => fun x : R => x ~= 0
| Strict => fun x : R => 0 < x
| NonStrict => fun x : R => 0 <= x
end.

Definition eval_nformula (env : Env) (f : NFormula) : Prop :=
let (p, op) := f in eval_op1 op (eval_pexpr env p).

Definition normalise (f : Formula) : NFormula :=
let (lhs, op, rhs) := f in
  match op with
  | OpEq => (PEsub lhs rhs, Equal)
  | OpNEq => (PEsub lhs rhs, NonEqual)
  | OpLe => (PEsub rhs lhs, NonStrict)
  | OpGe => (PEsub lhs rhs, NonStrict)
  | OpGt => (PEsub lhs rhs, Strict)
  | OpLt => (PEsub rhs lhs, Strict)
  end.

Definition negate (f : Formula) : NFormula :=
let (lhs, op, rhs) := f in
  match op with
  | OpEq => (PEsub rhs lhs, NonEqual)
  | OpNEq => (PEsub rhs lhs, Equal)
  | OpLe => (PEsub lhs rhs, Strict) (* e <= e' == ~ e > e' *)
  | OpGe => (PEsub rhs lhs, Strict)
  | OpGt => (PEsub rhs lhs, NonStrict)
  | OpLt => (PEsub lhs rhs, NonStrict)
end.

Theorem normalise_sound :
  forall (env : Env) (f : Formula),
    eval_formula env f -> eval_nformula env (normalise f).
Proof.
intros env f H; destruct f as [lhs op rhs]; simpl in *.
destruct op; simpl in *.
now apply <- (Rminus_eq_0 sor).
intros H1. apply -> (Rminus_eq_0 sor) in H1. now apply H.
now apply -> (Rle_le_minus sor).
now apply -> (Rle_le_minus sor).
now apply -> (Rlt_lt_minus sor).
now apply -> (Rlt_lt_minus sor).
Qed.

Theorem negate_correct :
  forall (env : Env) (f : Formula),
    eval_formula env f <-> ~ (eval_nformula env (negate f)).
Proof.
intros env f; destruct f as [lhs op rhs]; simpl.
destruct op; simpl.
symmetry. rewrite (Rminus_eq_0 sor).
split; intro H; [symmetry; now apply -> (Req_dne sor) | symmetry in H; now apply <- (Req_dne sor)].
rewrite (Rminus_eq_0 sor). split; intro; now apply (Rneq_symm sor).
rewrite <- (Rlt_lt_minus sor). now rewrite <- (Rle_ngt sor).
rewrite <- (Rlt_lt_minus sor). now rewrite <- (Rle_ngt sor).
rewrite <- (Rle_le_minus sor). now rewrite <- (Rlt_nge sor).
rewrite <- (Rle_le_minus sor). now rewrite <- (Rlt_nge sor).
Qed.

Definition OpMult (o o' : Op1) : Op1 :=
match o with
| Equal => Equal
| NonStrict => NonStrict (* (OpMult NonStrict Equal) could be defined as Equal *)
| Strict => o'
| NonEqual => NonEqual (* does not matter what we return here; see the following lemmas *)
end.

Definition OpAdd (o o': Op1) : Op1 :=
match o with
| Equal => o'
| NonStrict =>
  match o' with
  | Strict => Strict
  | _ => NonStrict
  end
| Strict => Strict
| NonEqual => NonEqual (* does not matter what we return here *)
end.

Lemma OpMultNonEqual :
  forall o o' : Op1, o <> NonEqual -> o' <> NonEqual -> OpMult o o' <> NonEqual.
Proof.
intros o o' H1 H2; destruct o; destruct o'; simpl; try discriminate;
try (intro H; apply H1; reflexivity);
try (intro H; apply H2; reflexivity).
Qed.

Lemma OpAdd_NonEqual :
  forall o o' : Op1, o <> NonEqual -> o' <> NonEqual -> OpAdd o o' <> NonEqual.
Proof.
intros o o' H1 H2; destruct o; destruct o'; simpl; try discriminate;
try (intro H; apply H1; reflexivity);
try (intro H; apply H2; reflexivity).
Qed.

Lemma OpMult_sound :
  forall (o o' : Op1) (x y : R), o <> NonEqual -> o' <> NonEqual ->
    eval_op1 o x -> eval_op1 o' y -> eval_op1 (OpMult o o') (x * y).
Proof.
unfold eval_op1; destruct o; simpl; intros o' x y H1 H2 H3 H4.
rewrite H3; now rewrite (Rtimes_0_l sor).
elimtype False; now apply H1.
destruct o'.
rewrite H4; now rewrite (Rtimes_0_r sor).
elimtype False; now apply H2.
now apply (Rtimes_pos_pos sor).
apply (Rtimes_nonneg_nonneg sor); [le_less | assumption].
destruct o'.
rewrite H4, (Rtimes_0_r sor); le_equal.
elimtype False; now apply H2.
apply (Rtimes_nonneg_nonneg sor); [assumption | le_less].
now apply (Rtimes_nonneg_nonneg sor).
Qed.

Lemma OpAdd_sound :
  forall (o o' : Op1) (e e' : R), o <> NonEqual -> o' <> NonEqual ->
    eval_op1 o e -> eval_op1 o' e' -> eval_op1 (OpAdd o o') (e + e').
Proof.
unfold eval_op1; destruct o; simpl; intros o' e e' H1 H2 H3 H4.
destruct o'.
now rewrite H3, H4, (Rplus_0_l sor).
elimtype False; now apply H2.
now rewrite H3, (Rplus_0_l sor).
now rewrite H3, (Rplus_0_l sor).
elimtype False; now apply H1.
destruct o'.
now rewrite H4, (Rplus_0_r sor).
elimtype False; now apply H2.
now apply (Rplus_pos_pos sor).
now apply (Rplus_pos_nonneg sor).
destruct o'.
now rewrite H4, (Rplus_0_r sor).
elimtype False; now apply H2.
now apply (Rplus_nonneg_pos sor).
now apply (Rplus_nonneg_nonneg sor).
Qed.

(* We consider a monoid whose generators are polynomials from the
hypotheses of the form (p ~= 0). Thus it follows from the hypotheses that
every element of the monoid (i.e., arbitrary product of generators) is ~=
0. Therefore, the square of every element is > 0. *)

Inductive Monoid (l : list NFormula) : PExprC -> Prop :=
| M_One : Monoid l (PEc cI)
| M_In : forall p : PExprC, In (p, NonEqual) l -> Monoid l p
| M_Mult : forall (e1 e2 : PExprC), Monoid l e1 -> Monoid l e2 -> Monoid l (PEmul e1 e2).

Inductive Cone (l : list (NFormula)) : PExprC -> Op1 -> Prop :=
| InC : forall p op, In (p, op) l -> op <> NonEqual -> Cone l p op
| IsIdeal : forall p, Cone l p Equal -> forall p', Cone l (PEmul p p') Equal
| IsSquare : forall p, Cone l (PEmul p p) NonStrict
| IsMonoid : forall p, Monoid l p -> Cone l (PEmul p p) Strict
| IsMult : forall p op q oq, Cone l p op -> Cone l q oq -> Cone l (PEmul p q) (OpMult op oq)
| IsAdd : forall p op q oq, Cone l p op -> Cone l q oq -> Cone l (PEadd p q) (OpAdd op oq)
| IsPos : forall c : C, cltb cO c = true -> Cone l (PEc c) Strict
| IsZ : Cone l (PEc cO) Equal.

(* As promised, if all hypotheses are true in some environment, then every
member of the monoid is nonzero in this environment *)

Lemma monoid_nonzero : forall (l : list NFormula) (env : Env),
  (forall f : NFormula, In f l -> eval_nformula env f) ->
    forall p : PExprC, Monoid l p -> eval_pexpr env p ~= 0.
Proof.
intros l env H1 p H2. induction H2 as [| f H | e1 e2 H3 IH1 H4 IH2]; simpl.
rewrite addon.(SORrm).(morph1). apply (Rneq_symm sor). apply (Rneq_0_1 sor).
apply H1 in H. now simpl in H.
simpl in IH1, IH2. apply (Rtimes_neq_0 sor). now split.
Qed.

(* If all members of a cone base are true in some environment, then every
member of the cone is true as well *)

Lemma cone_true :
  forall (l : list NFormula) (env : Env),
    (forall (f : NFormula), In f l -> eval_nformula env f) ->
      forall (p : PExprC) (op : Op1), Cone l p op ->
        op <> NonEqual /\ eval_nformula env (p, op).
Proof.
intros l env H1 p op H2. induction H2; simpl in *.
split. assumption. apply H1 in H. now unfold eval_nformula in H.
split. discriminate. destruct IHCone as [_ H3]. rewrite H3. now rewrite (Rtimes_0_l sor).
split. discriminate. apply (Rtimes_square_nonneg sor).
split. discriminate. apply <- (Rlt_le_neq sor). split. apply (Rtimes_square_nonneg sor).
apply (Rneq_symm sor). apply (Rtimes_neq_0 sor). split; now apply monoid_nonzero with l.
destruct IHCone1 as [IH1 IH2]; destruct IHCone2 as [IH3 IH4].
split. now apply OpMultNonEqual. now apply OpMult_sound.
destruct IHCone1 as [IH1 IH2]; destruct IHCone2 as [IH3 IH4].
split. now apply OpAdd_NonEqual. now apply OpAdd_sound.
split. discriminate. rewrite <- addon.(SORrm).(morph0). now apply cltb_sound.
split. discriminate. apply addon.(SORrm).(morph0).
Qed.

(* Every element of a monoid is a product of some generators; therefore,
to determine an element we can give a list of generators' indices *)

Definition MonoidMember : Set := list nat.

Inductive ConeMember : Type :=
| S_In : nat -> ConeMember
| S_Ideal : PExprC -> ConeMember -> ConeMember
| S_Square : PExprC -> ConeMember
| S_Monoid : MonoidMember -> ConeMember
| S_Mult : ConeMember -> ConeMember -> ConeMember
| S_Add : ConeMember -> ConeMember -> ConeMember
| S_Pos : forall c : C, cltb cO c = true -> ConeMember (* the proof of cltb 0 c = true should be (refl_equal true) *)
| S_Z : ConeMember.

Definition nformula_times (f f' : NFormula) : NFormula :=
let (p, op) := f in
  let (p', op') := f' in
    (PEmul p p', OpMult op op').

Definition nformula_plus (f f' : NFormula) : NFormula :=
let (p, op) := f in
  let (p', op') := f' in
    (PEadd p p', OpAdd op op').

Definition nformula_times_0 (p : PExprC) (f : NFormula) : NFormula :=
let (q, op) := f in
  match op with
  | Equal => (PEmul q p, Equal)
  | _ => f
  end.

Fixpoint eval_monoid (l : list NFormula) (ns : MonoidMember) {struct ns} : PExprC :=
match ns with
| nil => PEc cI
| n :: ns =>
  let p := match nth n l (PEc cI, NonEqual) with
           | (q, NonEqual) => q
           | _ => PEc cI
           end in
    PEmul p (eval_monoid l ns)
end.

Theorem eval_monoid_in_monoid :
  forall (l : list NFormula) (ns : MonoidMember), Monoid l (eval_monoid l ns).
Proof.
intro l; induction ns; simpl in *.
constructor.
apply M_Mult; [| assumption].
destruct (nth_in_or_default a l (PEc cI, NonEqual)).
destruct (nth a l (PEc cI, NonEqual)). destruct o; try constructor. assumption.
rewrite e; simpl. constructor.
Qed.

(* Provides the cone member from the witness, i.e., ConeMember *)
Fixpoint eval_cone (l : list NFormula) (cm : ConeMember) {struct cm} : NFormula :=
match cm with
| S_In n => match nth n l (PEc cO, Equal) with
            | (_, NonEqual) => (PEc cO, Equal)
            | f => f
            end
| S_Ideal p cm' => nformula_times_0 p (eval_cone l cm')
| S_Square p => (PEmul p p, NonStrict)
| S_Monoid m => let p := eval_monoid l m in (PEmul p p, Strict)
| S_Mult p q => nformula_times (eval_cone l p) (eval_cone l q)
| S_Add p q => nformula_plus (eval_cone l p) (eval_cone l q)
| S_Pos c _ => (PEc c, Strict)
| S_Z => (PEc cO, Equal)
end.

Theorem eval_cone_in_cone :
  forall (l : list NFormula) (cm : ConeMember),
    let (p, op) := eval_cone l cm in Cone l p op.
Proof.
intros l cm; induction cm; simpl.
destruct (nth_in_or_default n l (PEc cO, Equal)).
destruct (nth n l (PEc cO, Equal)). destruct o; try (now apply InC). apply IsZ.
rewrite e. apply IsZ.
destruct (eval_cone l cm). destruct o; simpl; try assumption. now apply IsIdeal.
apply IsSquare.
apply IsMonoid. apply eval_monoid_in_monoid.
destruct (eval_cone l cm1). destruct (eval_cone l cm2). unfold nformula_times. now apply IsMult.
destruct (eval_cone l cm1). destruct (eval_cone l cm2). unfold nformula_plus. now apply IsAdd.
now apply IsPos. apply IsZ.
Qed.

(* (inconsistent_cone_member l p) means (p, op) is in the cone for some op
(> 0, >= 0, == 0, or ~= 0) and this formula is inconsistent. This fact
implies that l is inconsistent, as shown by the next lemma. Inconsistency
of a formula (p, op) can be established by normalizing p and showing that
it is a constant c for which (c, op) is false. (This is only a sufficient,
not necessary, condition, of course.) Membership in the cone can be
verified if we have a certificate. *)

Definition inconsistent_cone_member (l : list NFormula) (p : PExprC) :=
  exists op : Op1, Cone l p op /\
    forall env : Env, ~ eval_op1 op (eval_pexpr env p).

Implicit Arguments make_impl [A].

(* If some element of a cone is inconsistent, then the base of the cone
is also inconsistent *)

Lemma prove_inconsistent :
  forall (l : list NFormula) (p : PExprC),
    inconsistent_cone_member l p -> forall env, make_impl (eval_nformula env) l False.
Proof.
intros l p H env.
destruct H as [o [wit H]].
apply -> make_conj_impl.
intro H1. apply H with env.
pose proof (@cone_true l env) as H2.
cut (forall f : NFormula, In f l -> eval_nformula env f). intro H3.
apply (proj2 (H2 H3 p o wit)). intro. now apply make_conj_in.
Qed.

Definition normalise_pexpr : PExprC -> PolC :=
  norm_aux cO cI cplus ctimes cminus copp ceqb.

Let Reqe := mk_reqe rplus rtimes ropp req
  sor.(SORplus_wd)
  sor.(SORtimes_wd)
  sor.(SORopp_wd).

Theorem normalise_pexpr_correct :
  forall (env : Env) (e : PExprC), eval_pexpr env e == eval_pol env (normalise_pexpr e).
intros env e. unfold eval_pexpr, eval_pol, normalise_pexpr.
apply (norm_aux_spec sor.(SORsetoid) Reqe (Rth_ARth sor.(SORsetoid) Reqe sor.(SORrt))
addon.(SORrm) addon.(SORpower) nil). constructor.
Qed.

(* Check that a formula f is inconsistent by normalizing and comparing the
resulting constant with 0 *)

Definition check_inconsistent (f : NFormula) : bool :=
let (e, op) := f in
  match normalise_pexpr e with
  | Pc c =>
    match op with
    | Equal => cneqb c cO
    | NonStrict => c [<] cO
    | Strict => c [<=] cO
    | NonEqual => false (* eval_cone never returns (p, NonEqual) *)
    end
  | _ => false (* not a constant *)
  end.

Lemma check_inconsistent_sound :
  forall (p : PExprC) (op : Op1),
    check_inconsistent (p, op) = true -> forall env, ~ eval_op1 op (eval_pexpr env p).
Proof.
intros p op H1 env. unfold check_inconsistent in H1.
destruct op; simpl; rewrite normalise_pexpr_correct;
destruct (normalise_pexpr p); simpl; try discriminate H1;
rewrite <- addon.(SORrm).(morph0).
now apply cneqb_sound.
apply cleb_sound in H1. now apply -> (Rle_ngt sor).
apply cltb_sound in H1. now apply -> (Rlt_nge sor).
Qed.

Definition check_normalised_formulas : list NFormula -> ConeMember -> bool :=
  fun l cm => check_inconsistent (eval_cone l cm).

Lemma checker_nf_sound :
  forall (l : list NFormula) (cm : ConeMember),
    check_normalised_formulas l cm = true ->
      forall env : Env, make_impl (eval_nformula env) l False.
Proof.
intros l cm H env.
unfold check_normalised_formulas in H.
case_eq (eval_cone l cm). intros p op H1.
apply prove_inconsistent with p. unfold inconsistent_cone_member. exists op. split.
pose proof (eval_cone_in_cone l cm) as H2. now rewrite H1 in H2.
apply check_inconsistent_sound. now rewrite <- H1.
Qed.

Definition check_formulas :=
  CheckerMaker.check_formulas normalise check_normalised_formulas.

Theorem check_formulas_sound :
  forall (l : list Formula) (w : ConeMember),
    check_formulas l w = true ->
      forall env : Env, make_impl (eval_formula env) l False.
Proof.
exact (CheckerMaker.check_formulas_sound eval_formula eval_nformula normalise
       normalise_sound check_normalised_formulas checker_nf_sound).
Qed.

Definition check_conj_formulas :=
  CheckerMaker.check_conj_formulas normalise negate check_normalised_formulas.

Theorem check_conj_formulas_sound :
  forall (l1 : list Formula) (l2 : list Formula) (ws : list ConeMember),
    check_conj_formulas l1 ws l2 = true ->
      forall env : Env, make_impl (eval_formula env) l1 (make_conj (eval_formula env) l2).
Proof.
exact (check_conj_formulas_sound eval_formula eval_nformula normalise negate
       normalise_sound negate_correct check_normalised_formulas checker_nf_sound).
Qed.

End Micromega.

