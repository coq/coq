Require Import List Arith Max Omega Bool Setoid Wf_nat.

Hint Extern 1 (?f _ = ?f _) => f_equal.
Hint Extern 1 (?f _ _ = ?f _ _) => f_equal.
Hint Extern 1 (?f _ _ _ = ?f _ _ _) => f_equal.


(** * Les termes *)

(** Encore plus mini que mini-ML : un lambda-calcul, toujours sans types *)
(** On laisse juste une constante TDummy, ca ne coute rien *)

Inductive term : Set :=
  | TDummy : term
  | TVar : nat -> term
  | TFun : term -> term
  | TApply : term -> term -> term
.

Notation "a @ b" := (TApply a b) (at level 40).

(** Les valeurs possibles apres evaluation : constantes ou clotures *)

Inductive value : Set:=
  | VDummy : value 
  | VClos : list value -> term -> value
.


(** Variables libres *)

(** Est-ce que n est libre dans t ? *)

Fixpoint freevar (n:nat)(t:term) { struct t } : bool := 
 match t with 
    | TDummy => false
    | TVar k => if eq_nat_dec k n then true else false
    | TFun t => freevar (S n) t
    | t1@t2 => (freevar n t1) || (freevar n t2)
 end.

(** Termes clos *)

Definition clos t := forall n, freevar n t = false.
Definition clos_list l := forall t, In t l -> clos t.

(** termes clos au dela d'un certain indice *)

Definition clos_after n t := forall m, n<=m -> freevar m t = false. 

(** Substitution de n par u dans t (pour un u forcement clos).
    Les indices au dela de n dans t sont decrementes de 1. *)

Fixpoint subst n u t {struct t} :=
  match t with
    | TDummy => TDummy
    | TVar k => 
        match lt_eq_lt_dec k n with
          | inleft (left _) => TVar k
          | inleft (right _) => u
          | inright _ => TVar (pred k)
        end
    | TFun t => TFun (subst (S n) u t)
    | t1@t2 => (subst n u t1)@(subst n u t2)
  end
.

Notation "t [ n := u ]" := (subst n u t) 
 (at level 20, n at next level, left associativity).

(** Substitution par paquet: 
    Si l = [u0;u1;...], on remplace n par u0, n+1 par u1, etc. 
    Les indices au dela de n+(length l) sont decrementes de (length l). *)

Fixpoint subst_list n l t {struct t} := match t with 
   | TDummy => TDummy 
   | TVar k => if (le_lt_dec n k) then nth (k-n) l (TVar (k-length l))
               else TVar k
   | TFun t => TFun (subst_list (S n) l t)
   | t1@t2 => (subst_list n l t1)@(subst_list n l t2)
  end
.

Notation "t [ n ::= l ]" := (subst_list n l t) 
 (at level 20, n at next level, left associativity).


(** Une presentation alternative de la substitution par paquet, 
    par iteration de subst *)

Fixpoint subst_list_iter n l t {struct l} := match l with
   | nil => t
   | u::l => subst_list_iter n l (t[n:=u])
  end
.

Notation "t [ n ;;= l ]" := (subst_list_iter n l t) 
 (at level 20, n at next level, left associativity).

(** Une definition alternative de la cloture *) 

Definition closbis t := forall n u, t[n:=u] = t.




(** Resultats concernant termes, cloture et substitutions. *)

Lemma term_dec : forall t u : term, { t = u } + { t<>u }.
Proof.
decide equality.
apply eq_nat_dec.
Qed.

Lemma clos_after_App1 : 
 forall n t1 t2, clos_after n (t1@t2) -> clos_after n t1.
Proof.
 unfold clos_after; simpl; intros.
 destruct (orb_false_elim _ _ (H _ H0)); auto.
Qed.

Lemma clos_after_App2 : 
 forall n t1 t2, clos_after n (t1@t2) -> clos_after n t2.
Proof.
 unfold clos_after; simpl; intros.
 destruct (orb_false_elim _ _ (H _ H0)); auto.
Qed.

Lemma clos_after_Fun : 
 forall n t, clos_after n (TFun t) -> clos_after (S n) t.
Proof.
 unfold clos_after; simpl; intros.
 assert (n <= m-1) by omega.
 replace m with (S (m-1)) by omega; auto.
Qed.

Lemma clos_list_cons : forall a l, clos_list (a::l) <-> clos a /\ clos_list l.
Proof.
 split.
 split.
 intros; apply (H a); simpl; auto.
 intros u Hu; apply (H u); simpl; auto.
 destruct 1; intros u Hu; simpl in Hu; destruct Hu; subst; auto.
Qed.

Lemma clos_list_app : forall l l', 
 clos_list (l++l') <-> clos_list l /\ clos_list l'.
Proof.
 induction l; simpl; auto.
 intuition.
 intros u Hu; inversion Hu.
 intros; do 2 rewrite clos_list_cons; rewrite IHl; intuition.
Qed.

Ltac dec := 
  let H := fresh "H" in 
  destruct lt_eq_lt_dec as [[H|H]|H] ||
  destruct le_lt_dec as [H|H] || 
  destruct eq_nat_dec as [H|H] || idtac; 
  simpl; 
  trivial; 
  try (intros; discriminate); 
  try (elimtype False; omega);
  match goal with 
    | H:?n=?n  |- _ => clear H
    | H:?n<=?n |- _ => clear H
    | _ => idtac
  end.

Ltac orb H :=  destruct (orb_false_elim _ _ H); auto.

(*
Ltac name_of te := 
 match goal with 
  | H : te |- _ => H
 end.
Tactic Notation "elim_on" constr(t):= let H:=name_of t in elim H.
*)

Lemma subst_clos_after : forall t n, 
   clos_after n t <-> (forall n0 t0, n <= n0 -> subst n0 t0 t = t).
Proof.
 induction t; unfold clos_after in *; simpl; intros.
 (* Dummy *)
 intuition.
 (* Var *)
 intuition; dec; subst.
 generalize (H _ H0); dec.
 assert (H' : n0 <= n) by omega; generalize (H _ H'); dec.
 generalize (H _ TDummy H0); dec.
 (* Fun *)
 destruct (IHt (S n)) as [IHa IHb]; clear IHt.
 split; intros.
 f_equal; apply IHa; auto with arith; intros.
 destruct m; auto with arith.
 inversion H1.
 apply IHb; auto with arith; intros.
 destruct n0; auto with arith.
 inversion H1.
 assert (H' : n <= n0) by omega; generalize (H _ t0 H'); congruence.
 (* Apply *)
 destruct (IHt1 n) as [IH1a IH1b]; clear IHt1.
 destruct (IHt2 n) as [IH2a IH2b]; clear IHt2.
 split; intros.
 f_equal; [apply IH1a | apply IH2a]; auto with arith; intros.
 orb (H _ H1).
 orb (H _ H1).
 rewrite IH1b; auto with arith; intros.
 rewrite IH2b; auto with arith; intros.
 generalize (H _ t0 H1); congruence.
 generalize (H _ t0 H1); congruence.
Qed.

Lemma clos_closbis : forall t, clos t <-> closbis t.
Proof.
 unfold clos, closbis; intros.
 destruct (subst_clos_after t 0); unfold clos_after in *.
 split; auto with arith.
Qed.

(** La consequence utile de tout ca: *)

Lemma subst_clos : forall t, clos t -> forall n u, t[n:=u] = t.
Proof.
 intros t H n u; rewrite clos_closbis in H; rewrite H; auto.
Qed.
Hint Resolve subst_clos.
Hint Extern 1 (?t=?t[_:=_]) => (symmetry; auto).

Lemma subst_list_clos : forall l t n, clos t -> t[n;;=l] = t.
Proof.
induction l; simpl; auto; intros.
rewrite (subst_clos _ H); auto.
Qed.
Hint Resolve subst_list_clos.
Hint Extern 1 (?t=?t[_;;=_]) => (symmetry; auto).

Lemma subst_freevar : forall t n u m, n <= m -> 
  clos u -> clos_after (S m) t -> clos_after m (t[n:=u]).
Proof.
unfold clos_after; induction t; simpl; auto; intros.
assert (~ S m <= n).
 intro H'; generalize (H1 _ H'); dec.
clear H1; do 3 dec.
apply IHt with (S m); auto with arith.
intros m1 Hm1.
replace m1 with (S (pred m1)) by omega; auto with arith.
apply orb_false_intro.
apply IHt1 with m; auto with arith.
intros m1 Hm1; orb (H1 _ Hm1).
apply IHt2 with m; auto with arith.
intros m1 Hm1; orb (H1 _ Hm1).
Qed.

Lemma subst_list_iter_freevar : forall l n t, 
  clos_list l -> 
  clos_after (n+length l) t -> 
  clos_after n (t[n;;=l]).
Proof.
induction l; simpl; auto; intros.
replace n with (n+0); auto with arith.
rewrite clos_list_cons in H; destruct H.
apply IHl; auto.
apply subst_freevar; auto with arith.
rewrite <- plus_n_Sm in H0; auto.
Qed.

Lemma subst_list_equiv : forall t l n, 
 clos_list l -> t[n;;=l] = t[n::=l].
Proof.
intros t l; revert t; induction l; simpl; auto; intros.
(* nil *)
clear H.
revert n; induction t; simpl; auto.
intro k; dec; destruct (n-k); auto with arith.
(* cons *)
rewrite clos_list_cons in H; destruct H.
assert (IH:=fun t n => IHl t n H0); clear IHl H0.
revert n; induction t; intros; rewrite IH; simpl; auto.
(* - var *)
rename n into k; rename n0 into n.
dec; dec.
 subst k; replace (n-n) with 0 by omega; simpl.
 rewrite <- IH; auto.
 replace (k-n) with (S (pred k - n)) by omega; simpl; dec.
 f_equal; f_equal; omega.
(* - fun *)
rewrite <- IHt; auto.
(* - app *)
rewrite <- IHt1; rewrite <- IHt2; auto.
Qed.

Lemma subst_commut : forall u u', clos u -> clos u' -> 
 forall t n n', n<=n' -> t[S n':=u'][n:=u] = t[n:=u][n':=u'].
Proof.
induction t; simpl; intros; auto with arith.
do 4 dec; auto.
Qed.
Hint Resolve subst_commut.

Lemma subst_list_iter_commut : forall l t u n, 
 clos u -> clos_list l -> 
 t[S n;;=l][n:=u] = t[n:=u][n;;=l].
Proof.
induction l; simpl; auto; intros.
rewrite clos_list_cons in H0; destruct H0.
rewrite IHl; auto.
Qed.
Hint Resolve subst_list_iter_commut.

Lemma subst_list_iter_commut2 : forall l t u u' n,  
 clos u -> clos u' -> clos_list l -> 
 t[S (S n);;=l][n:=u][n:=u'] = t[n:=u][n:=u'][n;;=l].
Proof.
induction l; simpl; auto; intros.
rewrite clos_list_cons in H1; destruct H1.
rewrite IHl; auto.
f_equal.
do 2 (rewrite <- (subst_commut u u'); auto).
rewrite <- (subst_commut u a); auto.
Qed.

Lemma subst_list_iter_commut3 : forall l l' t n, 
 clos_list l -> clos_list l' -> 
 t[(length l+n);;=l'][n;;=l] = t [n;;=l++l'].
Proof.
induction l; simpl; auto; intros.
rewrite clos_list_cons in H; destruct H; auto.
do 2 (rewrite <- subst_list_iter_commut; auto); f_equal.
replace (S (length l + n)) with (length l + (S n)) by omega; auto.
rewrite clos_list_app; auto.
Qed.







(** * I) Semantique big-step avec environnement : *)

(**  Le predicat d'evaluation d'un terme dans un environnement (liste de valeurs) *)

Reserved Notation "e |= t --> v" (at level 100, t at next level).

Inductive BigStep : list value -> term -> value -> Prop:=
  | BigStep_Dum : forall e,  e |= TDummy --> VDummy
  | BigStep_Var : forall n e v, nth_error e n = Some v -> (e|=TVar n --> v)
  | BigStep_Fun : forall e t, e |= TFun t --> VClos e t
  | BigStep_App : forall e e' t t1 t2 v v2,
     (e|=t1-->VClos e' t) -> 
     (e|=t2-->v2) -> 
     (v2::e'|=t-->v) -> 
     (e|=t1@t2-->v)
where "e |= t --> v" := (BigStep e t v).

Hint Constructors BigStep.

(** En cas de succes dans l'evaluation, une seule arrivee possible *)

Lemma BigStep_det : forall e t v, (e|=t-->v) -> forall v', (e|=t-->v') -> v = v'.
Proof.
 induction 1; inversion_clear 1; auto; try congruence.
 assert (A : VClos e' t = VClos e'0 t0) by auto.
 inversion A; subst e'0; subst t0; clear A.
 assert (A : v2 = v1) by auto.
 subst v2; auto.
Qed.




(** Termes avec environnement inclus *)

Inductive eterm : Set := 
 | EDummy : eterm 
 | EVar : nat -> eterm 
 | EFun : list value -> term -> eterm 
 | EApply : eterm -> eterm -> eterm.

Fixpoint v2et v := match v with 
 | VDummy => EDummy
 | VClos e t => EFun e t
end.

Lemma v2et_inj: forall v v', v2et v = v2et v' -> v = v'.
Proof.
destruct v; destruct v'; simpl; intros; try discriminate; congruence.
Qed.
Hint Resolve v2et_inj.

Lemma v2et_inj_list: forall vl vl', map v2et vl = map v2et vl' -> vl = vl'.
Proof.
induction vl; destruct vl'; simpl; intros; try discriminate; try congruence.
inversion H; subst; auto.
Qed.


Fixpoint t2et e t { struct t } := match t with 
 | TDummy => EDummy
 | TVar n => match nth_error e n with 
    | None => EVar (n-length e)
    | Some v => v2et v
   end
 | TFun t => EFun e t
 | t@u => EApply (t2et e t) (t2et e u)
end.

Fixpoint v2t v := match v with
 | VDummy => TDummy
 | VClos e f => TFun (subst_list_iter 1 (map v2t e) f)
end.

Fixpoint et2t t := match t with 
 | EDummy => TDummy
 | EVar n => TVar n
 | EFun e t => TFun (subst_list_iter 1 (map v2t e) t)
 | EApply t u => TApply (et2t t) (et2t u) 
end.

Lemma et2t_v2et : forall v, 
 et2t (v2et v) = v2t v.
Proof.
 induction v; simpl; auto.
Qed.




(** II) Semantique small-step avec environnements dans les termes *)

Reserved Notation "u --:> v" (at level 100).
Reserved Notation "u ==:> v" (at level 100).

Inductive ESmallStep : eterm -> eterm -> Prop := 
  | ESmallStep_beta : forall e t u v, u = v2et v -> 
     (EApply (EFun e t) u --:> t2et (v::e) t)
  | ESmallStep_app1 : forall u v t,
     (u--:>v) -> (EApply u t --:> EApply v t)
  | ESmallStep_app2 : forall u v t,
     (u--:>v) -> (EApply t u --:> EApply t v)
where "u --:> v" := (ESmallStep u v).

Hint Constructors ESmallStep.

Inductive ESmallSteps : eterm -> eterm -> Prop :=
  | ESmallSteps_refl : forall t, (t==:>t)
  | ESmallSteps_trans : forall t u r, (t--:>u) -> (u==:>r) -> (t==:>r)
where "u ==:> v" := (ESmallSteps u v).

Hint Constructors ESmallSteps.

Fixpoint ESmallStepN n := match n with 
  | O => fun t r => t=r
  | S n => fun t r => exists s, (t--:>s) /\ ESmallStepN n s r
 end.

Definition ESmallSteps' t u := exists n, ESmallStepN n t u.

Lemma ESmallSteps_alt : forall t u, (t==:>u) <-> ESmallSteps' t u.
Proof.
 split.
 induction 1.
 exists 0; simpl; auto.
 destruct IHESmallSteps as (n,H1).
 exists (S n); simpl; exists u; auto.
 destruct 1 as (n,H).
 revert t u H.
 induction n; simpl.
 intros; rewrite H; auto.
 destruct 1 as (s,(H1,H2)); eauto.
Qed.


Lemma ESmallStep_v2et : forall t u, (t--:>u) -> forall v, t = v2et v -> 
 u = v2et v.
Proof.
 induction 1; simpl; auto; intros; try (destruct v0; discriminate; fail).
Qed.

Lemma ESmallSteps_v2et : forall t u, (t==:>u) -> forall v, t = v2et v -> 
 u = v2et v.
Proof.
 induction 1; auto.
 intros.
 apply IHESmallSteps.
 eapply ESmallStep_v2et; eauto.
Qed.

Lemma ESmallSteps_trans2 : forall t u r,
  (t==:>u) -> (u==:>r) -> (t==:>r).
Proof.
  induction 1; intros; auto.
  eapply ESmallSteps_trans; eauto.
Qed.

Lemma ESmallStep_is_ESmallSteps : forall t u, (t--:>u) -> (t==:>u).
Proof.
  eauto.
Qed.

Lemma ESmallSteps_app1 : 
 forall t u r, (t==:>u) -> (EApply t r ==:> EApply u r).
Proof.
 induction 1; auto.
 eapply ESmallSteps_trans; eauto.
Qed.

Lemma ESmallSteps_app2 : 
 forall t u r, (t==:>u) -> (EApply r t ==:> EApply r u).
Proof.
 induction 1; auto.
 eapply ESmallSteps_trans; eauto.
Qed.

(**  I) -> II) *)

Lemma BigStep_ESmallSteps : forall e t v, 
  (e|=t-->v) -> (t2et e t ==:> v2et v).
Proof.
 induction 1; simpl; auto; intros.
 rewrite H; simpl; auto.
 eapply ESmallSteps_trans2.
 eapply ESmallSteps_app1; eauto.
 eapply ESmallSteps_trans2.
 eapply ESmallSteps_app2; eauto.
 eapply ESmallSteps_trans2; [ |eassumption].
 apply ESmallStep_is_ESmallSteps; simpl; auto.
Qed.





Lemma BigStep_v2et_t2et : forall v e t, v2et v = t2et e t -> (e|=t-->v).
Proof.
 induction v; simpl; auto; intros.

 destruct t; simpl in *; try discriminate; auto.
 constructor.
 destruct (nth_error e n); try discriminate.
 destruct v; try discriminate; auto.

 destruct t0; simpl in *; try discriminate; auto.
 constructor.
 destruct (nth_error e n); try discriminate.
 destruct v; simpl in *; try discriminate; inversion H; auto.
 inversion H; auto.
Qed.

Lemma ESmallStepN_inv_app : forall n t u v, 
ESmallStepN n (EApply t u) (v2et v) -> 
exists e0, exists t0, exists v0, exists n1, exists n2, exists n3, 
 S (n1+n2+n3) = n /\
 ESmallStepN n1 u (v2et v0) /\
 ((ESmallStepN n2 t (EFun e0 t0)  /\
   ESmallStepN n3 (t2et (v0::e0) t0) (v2et v))).
Proof.
induction n; simpl; intros.
destruct v; discriminate.
destruct H as (s,(Hs1,Hs2)).
inversion Hs1; clear Hs1; subst.

exists e; exists t0; exists v0; exists 0; exists 0; exists n.
repeat split; simpl; auto.

rename v0 into t'.
destruct (IHn _ _ _ Hs2) as (e1,(t1,(v1,(n1,(n2,(n3,(H,(H0,H1)))))))); clear IHn.
exists e1; exists t1; exists v1; exists n1; exists (S n2); exists n3.
repeat split; simpl; auto; destruct H1; auto.
omega.
exists t'; auto.

rename v0 into u'.
destruct (IHn _ _ _ Hs2) as (e1,(t1,(v1,(n1,(n2,(n3,(H,(H0,H1)))))))); clear IHn.
exists e1; exists t1; exists v1; exists (S n1); exists n2; exists n3.
repeat split; simpl; auto; destruct H1; auto.
exists u'; auto.
Qed.


Lemma ESmallStepN_BigStep : forall n t e v, 
  ESmallStepN n (t2et e t) (v2et v) -> 
  (e|=t-->v).
Proof.
 induction n using lt_wf_ind.
 induction t; simpl; auto; intros.

 destruct n; simpl in *.
 destruct v; try discriminate; auto.
 destruct H0 as (x,(Hx,Hx')).
 inversion Hx.

 constructor.
 destruct (nth_error e n0).
 f_equal.
 apply v2et_inj.
 symmetry.
 apply (ESmallSteps_v2et (v2et v0) (v2et v)); auto.
 rewrite ESmallSteps_alt.
 exists n; auto.
 destruct n; simpl in *.
 destruct v; discriminate.
 destruct H0 as (x,(Hx,Hx')).
 inversion Hx.

 destruct n; simpl in *; auto.
 destruct v; simpl in *; try discriminate.
 inversion H0; constructor; auto.
 destruct H0 as (x,(Hx,Hx')).
 inversion Hx.

 destruct (ESmallStepN_inv_app _ _ _ _ H0) as (e',(t',(v',(n1,(n2,(n3,H3)))))).
 intuition.
 apply BigStep_App with e' t' v'.
 eapply (H n2); eauto; omega.
 eapply (H n1); eauto; omega.
 eapply (H n3); eauto; omega.
Qed.

(** II) -> I) *)

Lemma ESmallSteps_BigStep : forall e t v, 
  (t2et e t ==:> v2et v) -> (e|=t-->v).
Proof.
intros.
rewrite ESmallSteps_alt in H.
destruct H.
eapply ESmallStepN_BigStep; eauto.
Qed.





(** III) Semantique small-step completement sans environnement *)

Inductive IsValue : term -> Prop := 
  | IsValue_Dummy : IsValue TDummy 
  | IsValue_Fun : forall t, IsValue (TFun t).

Hint Constructors IsValue.

Reserved Notation "u --> v" (at level 100).
Reserved Notation "u ==> v" (at level 100).

Inductive SmallStep : term -> term -> Prop :=
  | SmallStep_beta : forall t1 t2, 
      IsValue t2 -> ((TFun t1)@t2 --> t1[0:=t2])
  | SmallStep_app1 : forall u v t, (u-->v) -> (u@t-->v@t)
  | SmallStep_app2 : forall u v t, (u-->v) -> (t@u-->t@v)
where "t --> u" := (SmallStep t u).

Hint Constructors SmallStep.

Inductive SmallSteps : term -> term -> Prop :=
  | SmallSteps_refl : forall t, (t==>t)
  | SmallSteps_trans : forall t u r, (t-->u) -> (u==>r) -> (t==>r)
where "t ==> u" := (SmallSteps t u).

Hint Constructors SmallSteps.

Fixpoint SmallStepN n := match n with 
  | O => fun t r => t=r
  | S n => fun t r => exists s, (t-->s) /\ SmallStepN n s r
 end.

Definition SmallSteps' t u := exists n, SmallStepN n t u.

Lemma SmallSteps_SmallSteps' : forall t u, (t==>u) <-> SmallSteps' t u.
Proof.
 split.
 induction 1.
 exists 0; simpl; auto.
 destruct IHSmallSteps as (n,H1).
 exists (S n); simpl; exists u; auto.
 destruct 1 as (n,H).
 revert t u H.
 induction n; simpl.
 intros; rewrite H; auto.
 destruct 1 as (s,(H1,H2)); eauto.
Qed.





Lemma SmallSteps_trans2 : forall t u r,
  (t==>u) -> (u==>r) -> (t==>r).
Proof.
  induction 1; intros; auto.
  eapply SmallSteps_trans; eauto.
Qed.

Lemma SmallStep_is_SmallSteps : forall t u,
  (t-->u) -> (t==>u).
Proof.
  eauto.
Qed.

Lemma SmallSteps_app1 : forall t u r, (t==>u) -> (t@r==>u@r).
Proof.
 induction 1; auto.
 eapply SmallSteps_trans; eauto.
Qed.

Lemma SmallSteps_app2 : forall t u r, (t==>u) -> (r@t==>r@u).
Proof.
 induction 1; auto.
 eapply SmallSteps_trans; eauto.
Qed.

Lemma IsValue_v2t : forall v, IsValue (v2t v).
Proof.
 induction v; simpl; auto.
Qed.

Lemma IsValue_exists_value : forall t, IsValue t <-> exists v, v2t v=t.
Proof. 
 split; intros.
 induction H; auto; intros.
 exists VDummy; auto.
 exists (VClos nil t); simpl; auto.
 destruct H as (v,Hv).
 subst; apply IsValue_v2t.
Qed.

Hint Resolve IsValue_v2t.

Inductive val_clos : value -> Prop := 
 | clos_VDummy : val_clos VDummy
 | clos_Vclos : forall e t, env_clos e -> 
                            clos_after (S (length e)) t ->
                            val_clos (VClos e t)
with env_clos : list value -> Prop := 
 | clos_nil : env_clos nil 
 | clos_cons : forall v e, val_clos v -> env_clos e -> env_clos (v::e).

Hint Constructors val_clos env_clos.

Scheme val_clos_ind2 := Minimality for val_clos Sort Prop 
with env_clos_ind2 := Minimality for env_clos Sort Prop.

Lemma env_clos_app : 
 forall e1 e2, env_clos e1 -> env_clos e2 -> env_clos (e1++e2).
Proof.
 induction e1; simpl; auto.
 inversion_clear 1; intros.
 constructor; auto.
Qed.

Lemma v2t_clos : forall v, val_clos v -> clos (v2t v). (* RECIPROQUE FAUSSE ! *)
Proof.
 apply (val_clos_ind2 
         (fun v => clos (v2t v)) 
         (fun e => forall t, In t (map v2t e) -> clos t)); 
 simpl; auto; intros.
 
 red; simpl; auto.

 red; intros; simpl.
 apply subst_list_iter_freevar; auto with arith.
 red; intros.
 apply H1.
 rewrite map_length in H2; omega.

 contradiction.
 
 intuition.
 subst t; auto.
Qed.

Hint Resolve v2t_clos.

Lemma env_ok: forall e, env_clos e -> clos_list (map v2t e). (* RECIPROQUE FAUSSE *)
Proof.
induction e; unfold clos_list in *; simpl; auto.
contradiction.
inversion_clear 1.
destruct 1; auto.
subst t; apply v2t_clos; auto.
Qed.

Hint Resolve env_ok.

Definition do_env_subst e := subst_list 0 (map v2t e).  

Lemma do_env_subst_clos : 
 forall e t, env_clos e -> clos t -> do_env_subst e t = t. 
Proof.
intros.
unfold do_env_subst.
rewrite <- subst_list_equiv.
apply subst_list_clos; auto.
apply env_ok; auto.
Qed.

Definition SmallStepNormal t := forall u, ~(t-->u).

Lemma v2t_normal : forall v, SmallStepNormal (v2t v).
Proof.
induction v; simpl; intros; red; red; inversion 1.
Qed. 

Lemma BigStep_val_clos : 
 forall e t v, 
   (e |= t --> v) -> env_clos e -> clos_after (length e) t -> val_clos v.
Proof.
 induction 1; simpl; intros; auto.
 
 clear H1; revert n H0 H; induction e; destruct n; simpl; auto; intros; try discriminate.
 inversion H; auto.
 inversion_clear H0; subst; auto.
 inversion_clear H0; eauto. 
 
 constructor; auto.
 apply clos_after_Fun; auto.

 assert (val_clos (VClos e' t)).
  apply IHBigStep1; auto.
  eapply clos_after_App1; eauto.
 inversion_clear H4.
 assert (env_clos (v2::e')).
  constructor; auto.
  apply IHBigStep2; auto.
  eapply clos_after_App2; eauto.
 apply IHBigStep3; auto.
Qed.

Lemma et2t_t2et : 
 forall t e, env_clos e -> et2t (t2et e t) = do_env_subst e t.
Proof.
 induction t; unfold do_env_subst in *; simpl; auto; intros.
 
 replace (n-0) with n by omega.
 revert n; induction e; destruct n; simpl; auto.
 apply et2t_v2et.
 inversion_clear H; auto.
 
 f_equal; auto; rewrite subst_list_equiv; auto.
Qed.

Inductive eclos : eterm -> Prop := 
 | eclos_EDummy : eclos EDummy
 | eclos_EFun : 
    forall e t, env_clos e -> clos_after (S (length e)) t -> eclos (EFun e t)
 | eclos_EApply : 
    forall t u, eclos t -> eclos u -> eclos (EApply t u).

Hint Constructors eclos.

Lemma eclos_clos_val_1 : forall v, eclos (v2et v) -> val_clos v.
Proof.
 destruct v; simpl in *; auto; intros.
 inversion H; auto.
Qed.

Lemma eclos_clos_val_2 : forall v, val_clos v -> eclos (v2et v).
Proof.
 destruct v; simpl in *; auto; intros.
 inversion H; auto.
Qed.

Hint Resolve eclos_clos_val_1 eclos_clos_val_2.

Lemma ESmallStep_SmallStep : forall t u,
 ESmallStep t u -> eclos t -> (et2t t --> et2t u).
Proof.
 induction 1; simpl; intros; auto.
 subst u.
 inversion_clear H0.
 inversion_clear H.
 rewrite et2t_t2et.
 rewrite et2t_v2et.
 unfold do_env_subst.
 rewrite <- subst_list_equiv; simpl.
 rewrite <- subst_list_iter_commut; auto.

 red; intros.
 simpl in H; destruct H.
 subst t0; auto.
 revert t0 H; change (clos_list (map v2t e)).
 apply env_ok; auto.
 constructor; auto.

 inversion_clear H0; auto.

 inversion_clear H0; auto.
Qed.

Lemma eclos_t2et : forall t e, env_clos e -> clos_after (length e) t -> 
 eclos (t2et e t).
Proof.
 induction t; simpl; intros.
 constructor.
 red in H0; simpl in H0.
 assert (~(length e <= n)).
  generalize (H0 n).
  destruct (eq_nat_dec n n).
  intros; intro.
  assert (H3:= H1 H2); discriminate.
  elim n0; auto.
 assert (n<length e) by omega.
 clear H0 H1.
 revert n H H2; clear; induction e; simpl; intros.
 inversion H2.
 inversion_clear H.
 destruct n; simpl; auto with arith.

 constructor; auto.
 apply clos_after_Fun; auto.

 constructor; auto.
 apply IHt1; auto.
 eapply clos_after_App1; eauto.
 apply IHt2; auto.
 eapply clos_after_App2; eauto.
Qed.

Lemma ESmallStep_eclos : forall t u, ESmallStep t u -> eclos t -> eclos u.
Proof.
 induction 1; simpl; intros; auto.
 inversion_clear H0.
 inversion_clear H1.

 subst u; apply eclos_t2et; auto.

 inversion_clear H0; auto.
 inversion_clear H0; auto.
Qed.

(* II) -> III) *)

Lemma ESmallSteps_SmallSteps : forall t u,
 ESmallSteps t u -> eclos t -> (et2t t ==> et2t u).
Proof.
induction 1; auto; intros.
econstructor.
eapply ESmallStep_SmallStep; eauto.
apply IHESmallSteps.
eapply ESmallStep_eclos; eauto.
Qed.





(* Ce CBV est _tres_ confluent, heureusement, vu que 
   l'ordre des calculs est quasi deterministe  *)

Lemma SmallStep_Church_Rosser: forall a b c, (a-->b) -> (a-->c) -> 
 b<>c -> exists d, (b-->d) /\ (c-->d).
Proof.
induction a; intros.
inversion H.
inversion H.
inversion H.
inversion H; inversion H0; clear H H0; subst.

inversion H6; clear H6; subst.
elim H1; auto.

inversion H9.

elimtype False.
revert H5 H9; clear; induction 1; inversion 1.

inversion H5.

destruct (IHa1 v v0) as (d,(Hd1,Hd2)); auto.
exists (d@a2); auto.

exists (v@v0); auto.

elimtype False.
revert H5 H9; clear; induction 1; inversion 1.

exists (v0@v); auto.

destruct (IHa2 v v0) as (d,(Hd1,Hd2)); auto.
exists (a1@d); auto.
Qed.

Lemma SmallStepN_Church_Rosser_aux: forall n a b, SmallStepN n a b -> 
 forall c, (a-->c) -> 
 exists m, exists d, (b=d \/ (b-->d)) /\ SmallStepN m c d /\ m <= n.
Proof.
induction n; intros.
simpl in H; subst b.
exists 0; exists c; simpl; auto.
simpl in H; destruct H as (d,(Hd1,Hd2)).
destruct (term_dec c d).
subst c.
exists n; exists b; auto.
destruct (SmallStep_Church_Rosser _ _ _ Hd1 H0) as (e,(He1,He2)); auto.
destruct (IHn _ _ Hd2 _ He1) as (m,(f,(Hf1,(Hf2,Hf3)))).
exists (S m); exists f; split; auto; split; auto with arith.
exists e; auto.
Qed.

Lemma SmallStepN_Church_Rosser: forall n m a b c, SmallStepN n a b -> 
 SmallStepN m a c -> 
 exists n', exists m', exists d, SmallStepN m' b d /\ SmallStepN n' c d /\ n'<=n /\ m'<=m.
Proof.
induction n; intros.
simpl in H; subst; exists 0; exists m; exists c; simpl; auto.
simpl in H; destruct H as (d,(Hd1,Hd2)).
destruct (SmallStepN_Church_Rosser_aux _ _ _ H0 _ Hd1) as (m',(e,(He1,(He2,He3)))).
destruct (IHn _ _ _ _ Hd2 He2) as (n',(m'',(f,(Hf1,(Hf2,(Hf3,Hf4)))))).
destruct He1.
subst e.
exists n'; exists m''; exists f; repeat (split; auto with arith).
omega.
exists (S n'); exists m''; exists f; repeat (split; auto with arith).
exists e; auto.
omega.
Qed.

Lemma SmallStepN_unique_nf : forall n a b, SmallStepN n a b -> SmallStepNormal b -> 
 forall c, SmallStep a c -> exists p, SmallStepN p c b /\ p < n.
Proof.
induction n; intros.
simpl in H; subst b.
elim (H0 _ H1).
simpl in H; destruct H as (d,(Hd1,Hd2)).
destruct (term_dec c d).
subst d.
exists n; auto with arith.
destruct (SmallStep_Church_Rosser _ _ _ H1 Hd1 n0) as (e,(He1,He2)); auto.
destruct (IHn _ _ Hd2 H0 _ He2) as (p,(Hp1,Hp2)).
exists (S p); split; auto with arith.
exists e; auto.
Qed.

Axiom Excluded_Middle_ESmallStep: 
 forall t, (exists u, ESmallStep t u) \/ (forall u, ~ ESmallStep t u).


Lemma SmallStep_ESmallStep_notnormal : forall t u, SmallStep t u -> 
 forall t', et2t t' = t -> exists u', ESmallStep t' u'.
Proof.
induction 1; simpl; intros; auto.

destruct t'; simpl in H0; try discriminate.
inversion H0; clear H0; subst.
destruct t'1; simpl in H2; try discriminate.
inversion H2; clear H2; subst.
assert (exists v, v2et v = t'2).
 revert H; clear.
 destruct t'2; simpl; try (inversion 1; fail).
 intros; exists VDummy; auto.
 intros; exists (VClos l t); auto.
destruct H0 as (v, Hv).
eauto.

destruct t'; simpl in H0; try discriminate.
inversion H0; clear H0; subst.
destruct (IHSmallStep t'1) as (u,Hu); auto.
exists (EApply u t'2); auto.

destruct t'; simpl in H0; try discriminate.
inversion H0; clear H0; subst.
destruct (IHSmallStep t'2) as (u,Hu); auto.
exists (EApply t'1 u); auto.
Qed.


Lemma SmallStepN_ESmallSteps : forall n t u, SmallStepN n (et2t t) u -> eclos t ->
 SmallStepNormal u -> 
 exists u', ESmallSteps t u' /\ et2t u' = u.
Proof.
induction n using lt_wf_ind; intros.
destruct (Excluded_Middle_ESmallStep t).
destruct H3 as (t', Ht').
assert (H4:=ESmallStep_SmallStep _ _ Ht' H1).
destruct (SmallStepN_unique_nf _ _ _ H0 H2 _ H4) as (p,(Hp1,Hp2)).
assert (H5:=ESmallStep_eclos _ _ Ht' H1).
destruct (H _ Hp2 _ _ Hp1 H5 H2) as (u',(Hu1,Hu2)).
exists u'; split; auto.
econstructor; eauto.

destruct n.
simpl in *; subst u.
exists t; auto.
simpl in H0; destruct H0 as (u0,(Hu1,Hu2)).
destruct (SmallStep_ESmallStep_notnormal _ _ Hu1 t); auto.
elim (H3 _ H0).
Qed.

(** III) -> II) *)

Lemma SmallSteps_ESmallSteps : forall t u, SmallSteps t u -> clos t ->
 SmallStepNormal u -> 
 exists u', ESmallSteps (t2et nil t) u' /\ et2t u' = u.
Proof.
intros.
rewrite SmallSteps_SmallSteps' in H.
destruct H as (n,H).
apply (SmallStepN_ESmallSteps n (t2et nil t) u); auto.
rewrite et2t_t2et; simpl; auto.
unfold do_env_subst.
rewrite <- subst_list_equiv; simpl; auto.
red; inversion 1.
apply eclos_t2et; simpl; auto.
red; intros; apply H0; auto.
Qed.

(** III) -> I) *)

Lemma SmallSteps_BigStep : forall t u, (t==>u) -> clos t -> IsValue u -> 
 exists v, (nil |= t --> v) /\ v2t v = u.
Proof.
 intros.
 destruct (SmallSteps_ESmallSteps _ _ H H0).
 intros r Hr.
 inversion H1; subst; inversion Hr.
 destruct H2.
 assert (exists v', x = v2et v' /\ v2t v' = u).
  inversion H1; subst; simpl in *.
  destruct x; simpl in *; try discriminate; auto.
  exists VDummy; auto.
  destruct x; simpl in *; try discriminate; auto.
  exists (VClos l t1); split; simpl; auto.
 destruct H4 as (v,(Hv1,Hv2)).
 exists v; split; auto.
 apply ESmallSteps_BigStep.
 subst; auto.
Qed.



****************** END USEFUL STUFFS **********************







(* In closures, the env used as explicit substitution leads to 
   non-canonical representations of the "same" values. 
   We compensate this with the following equivalence relation. *)

Definition eqv (v v':value) : Prop := [|v|] = [|v'|].

Infix "~~" := eqv (at level 70, no associativity).

Lemma eqv_refl : forall v, v~~v.
Proof. red; auto. Qed.

Lemma eqv_sym : forall v1 v2, v1~~v2 -> v2~~v1.
Proof. red; auto. Qed.

Lemma eqv_trans : forall v1 v2 v3, v1~~v2 -> v2~~v3 -> v1~~v3.
Proof. unfold eqv; intros; eapply trans_eq; eauto. Qed.

Hint Resolve eqv_refl eqv_trans.
Hint Immediate eqv_sym.

Lemma eq_eqv : forall v1 v2, v1 = v2 -> v1 ~~ v2.
Proof. intros; subst; auto. Qed.

Hint Resolve eq_eqv.

Add Relation value eqv 
  reflexivity proved by eqv_refl
  symmetry proved by eqv_sym
  transitivity proved by eqv_trans
  as equiv_val_setoid.


(* Maintenant inutile ? *)

Inductive BigStepbis : term -> term -> Prop:=
  | BigStepbis_Dummy_base : BigStepbis TDummy TDummy
  | BigStepbis_Fun : forall t, BigStepbis (TFun t) (TFun t)
  | BigStepbis_Fix : forall t, BigStepbis (TFix t) (TFix t)
  | BigStepbis_let : forall t1 t2 v1 v ,
                           BigStepbis t1 v1 ->
                           BigStepbis t2[0:=v1] v ->
                           BigStepbis (TLet t1 t2) v
  | BigStepbis_app : forall t t1 t2 v v2,
                            BigStepbis t1 (TFun t) ->
                            BigStepbis t2 v2 ->
                            BigStepbis t[0:=v2] v ->
                            BigStepbis (TApply t1 t2) v
  | BigStepbis_appr : forall t t1 t2 v v2,
                            BigStepbis t1 (TFix t) ->
                            BigStepbis t2 v2 ->
                            BigStepbis t[0:=v2][0:=TFix t] v ->
                            BigStepbis (TApply t1 t2) v
  | BigStepbis_constr : forall tl vl n ,
                            BigStepbis_list tl vl -> 
                            BigStepbis (TConstr n tl) (TConstr n vl)
  | BigStepbis_match : forall t n pl vl m tn v,
                            BigStepbis t (TConstr n vl) ->
                            nth_error pl n = Some (Patc m tn) ->
                            length vl = m ->
                            BigStepbis (subst_list 0 (rev vl) tn) v ->
                            BigStepbis (TMatch t pl) v
with
BigStepbis_list : list term-> list term ->Prop:=
   | BigStepbis_nil : BigStepbis_list nil nil
   | BigStepbis_cons : forall t lt v lv , BigStepbis t v -> BigStepbis_list lt lv ->
                                          BigStepbis_list (t::lt) (v::lv)
.

Hint Constructors BigStepbis BigStepbis_list.

Scheme BigStepbis_ind2 := Minimality for BigStepbis Sort Prop 
with BigStepbis_list_ind2 := Minimality for BigStepbis_list Sort Prop.


Lemma BigStepbis_IsValue : forall t v, BigStepbis t v -> IsValue v.
Proof.
apply (BigStepbis_ind2 (fun t => IsValue) (fun lt => IsValue_list)); auto.
Qed.

Lemma BigStepbis_IsValue_list : forall tl vl, BigStepbis_list tl vl -> IsValue_list vl.
Proof.
apply (BigStepbis_list_ind2 (fun t => IsValue) (fun lt => IsValue_list)); auto.
Qed.

Lemma IsValue_BigStepbis : forall v, IsValue v -> BigStepbis v v.
Proof.
apply (IsValue_ind2 (fun v => BigStepbis v v) (fun lv => BigStepbis_list lv lv)); auto.
Qed.

Lemma IsValue_BigStepbis_list : forall vl, IsValue_list vl -> BigStepbis_list vl vl.
Proof.
apply (IsValue_list_ind2 (fun v => BigStepbis v v) (fun lv => BigStepbis_list lv lv)); auto.
Qed.

Hint Resolve BigStepbis_IsValue BigStepbis_IsValue_list IsValue_BigStepbis IsValue_BigStepbis_list.

Lemma BigStepbis_SmallSteps : forall t v, BigStepbis t v -> (t ==> v).
Proof.
 set (P:=fun t v => t ==> v).
 set (Q:=fix Q (lt:list term) lv { struct lt } := match lt, lv with 
          | nil, nil => True
          | t::lt,v::lv => P t v /\ Q lt lv
          | _, _ => False 
         end).
 apply (BigStepbis_ind2 P Q); red; auto.
 (* TLet *)
 unfold P in *; simpl; intros.
 apply SmallSteps_trans2 with (TLet v1 t2).
 generalize H0; clear; induction 1; auto.
 eapply SmallSteps_trans; eauto.
 eapply SmallSteps_trans; eauto.
 (* TApply *)
 unfold P; simpl; intros.
 apply SmallSteps_trans2 with (t1 @ v2).
 apply SmallSteps_app2; auto.
 apply SmallSteps_trans2 with (TFun t @ v2).
 apply SmallSteps_app1; auto.
 econstructor; eauto.
 (* TAppr *)
 unfold P; simpl; intros.
 apply SmallSteps_trans2 with (t1 @ v2).
 apply SmallSteps_app2; auto.
 apply SmallSteps_trans2 with (TFix t @ v2).
 apply SmallSteps_app1; auto.
 econstructor; eauto.
 (* TMatch *)
 intros.
 revert vl H0 H.
 induction tl; destruct vl; simpl in *; auto; try contradiction.
 destruct 1; intros.
 unfold P in H.
 inversion_clear H1.
 apply SmallSteps_constr; auto.
 (* Iota1 *)
 unfold P in *; intros.
 apply SmallSteps_trans2 with (TMatch (TConstr n vl) pl).
 apply SmallSteps_case; auto.
 apply SmallSteps_trans with (subst_list 0 (rev vl) tn); auto.
 constructor; auto.
 subst m; auto.
 generalize (BigStepbis_IsValue _ _ H).
 inversion_clear 1; auto.
Qed. 


Lemma SmallSteps_BigStepbis : forall t v, (t==>v) -> IsValue v -> BigStepbis t v.
Proof.
induction 1.
apply (IsValue_ind2 (fun t => BigStepbis t t) (fun l => BigStepbis_list l l)); auto.
intros.
generalize (IHSmallSteps H1); clear IHSmallSteps H0.
revert H t3 H1.
apply (SmallStep_ind2 
        (fun t1 t2 => forall t3, IsValue t3 -> BigStepbis t2 t3 -> BigStepbis t1 t3)
        (fun tl1 tl2 => forall tl3, 
           IsValue_list tl3 -> BigStepbis_list tl2 tl3 -> BigStepbis_list tl1 tl3)); 
intros.

eauto.

eauto.

eauto.

eauto.

inversion_clear H2.
eapply BigStepbis_app; eauto.
eapply BigStepbis_appr; eauto.

inversion_clear H2.
eapply BigStepbis_app; eauto.
eapply BigStepbis_appr; eauto.

inversion_clear H2.
eapply BigStepbis_let; eauto.

inversion_clear H2.
eapply BigStepbis_match; eauto.

inversion_clear H2.
eapply BigStepbis_constr; eauto.

inversion_clear H2; eauto.

inversion_clear H2; eauto.
Qed.

Lemma BigStep_BigStepbis : forall e t v,  
  (e |= t --> v) -> env_clos e -> clos_after (length e) t -> 
  (BigStepbis (do_env_subst e t) [|v|]).
Proof.
 set (P:=fun e t v => env_clos e -> clos_after (length e) t -> (BigStepbis (do_env_subst e t) [|v|])).
 set (Q:=fun e tl vl => env_clos e -> clos_after (length e) (TConstr 0 tl) -> 
           (BigStepbis_list (map (do_env_subst e) tl) (map v2t vl))).
 apply (BigStep_ind2 P Q); unfold do_env_subst in *; red; simpl; intros.
 (* TDummy *)
 auto.
 (* TVar *)
 rewrite map_length.
 replace (n-0) with n by auto with arith.
 assert (nth n (map v2t e) (TVar (n - length e)) = [|v|]).
  clear H1; revert n H; clear; induction e.
  destruct n; simpl; intros; discriminate.
  destruct n; simpl; intros; auto.
  inversion H; subst; auto.
 rewrite H2; apply IsValue_BigStepbis.
 apply IsValue_v2t.
 (* TFun *) 
 rewrite subst_list_equiv; auto. 
 (* TFix *)
 rewrite subst_list_equiv; auto.
 (* TLet *)
 unfold P in *; clear P Q.
 econstructor.
 eapply H0; auto.
 eapply clos_after_Let1; eauto.
 assert (env_clos (v1::e)).
  constructor; auto.
  eapply BigStep_val_clos; eauto.
  eapply clos_after_Let1; eauto.
 rewrite subst_list_equiv; auto.
 rewrite subst_list_equiv in H2; auto; simpl in H2.
 rewrite subst_subst_list_commut.
 apply H2; auto.
 eapply clos_after_Let2; eauto.
 inversion_clear H5; apply v2t_clos; auto.
 apply env_ok; auto.
 (* TApply *)
 unfold P in *; clear P Q.
 simpl in *.
 econstructor.
 eapply H0; eauto.
 eapply clos_after_App1; eauto.
 eapply H2; eauto.
 eapply clos_after_App2; eauto.
 assert (val_clos (VClos e' t)).
  eapply BigStep_val_clos; eauto.
  eapply clos_after_App1; eauto.
 assert (env_clos (v2::e')).
  constructor; auto.
  eapply BigStep_val_clos; eauto.
  eapply clos_after_App2; eauto.
  inversion_clear H7; auto.
 rewrite subst_list_equiv in H4; auto; simpl in H4.
 rewrite subst_subst_list_commut.
 apply H4; auto.
 inversion_clear H7; auto.
 inversion_clear H8; apply v2t_clos; auto.
 inversion_clear H7; apply env_ok; auto.
 change (clos_list (map v2t (v2::e'))).
 apply env_ok; auto.
 (* Appr *)
 unfold P in *; clear P Q.
 simpl in *.
 eapply BigStepbis_appr.
 eapply H0; eauto.
 eapply clos_after_App1; eauto.
 eapply H2; eauto.
 eapply clos_after_App2; eauto.
 assert (val_clos (VClos_rec e' t)).
  eapply BigStep_val_clos; eauto.
  eapply clos_after_App1; eauto.
 assert (env_clos (v2::VClos_rec e' t::e')).
  constructor; auto.
  eapply BigStep_val_clos; eauto.
  eapply clos_after_App2; eauto.
  inversion_clear H7; auto.
  constructor; auto.
  constructor; auto.
 rewrite subst_list_equiv in H4; auto; simpl in H4.
 rewrite subst_subst_list_commut2.
 apply H4; auto.
 inversion_clear H7; auto.
 inversion_clear H8; apply v2t_clos; auto.
 exact (v2t_clos  _ H7).
 inversion_clear H8; inversion_clear H10; apply env_ok; auto.
 exact (env_ok _ H8). 
 (* TConstr *)
 constructor.
 apply H0; auto.
 (* TMatch *)
 unfold P in *; simpl in *; clear P Q.
 eapply BigStepbis_match with (tn:=subst_list (m + 0) (map v2t e) tn); eauto.
 apply H0; auto.
 eapply clos_after_Match1; eauto.
 rewrite map_length; rewrite H2.
 revert H1; clear; revert n; induction pl; destruct n; simpl; auto; intros; try discriminate.
 inversion H1; subst a.
 unfold Specif.value; f_equal; f_equal; auto with arith.
 assert (val_clos (VConstr n vl)).
  eapply BigStep_val_clos; eauto.
  eapply clos_after_Match1; eauto.
 inversion_clear H7.
 rewrite subst_list_equiv; auto.
 rewrite subst_list_equiv; auto.
 rewrite subst_list_equiv in H4; auto; simpl in H4.
 rewrite map_app in H4.
 rewrite <- map_rev.
 rewrite <- subst_subst_list_commut3 in H4.
 rewrite map_length in H4; rewrite rev_length in H4; rewrite H2 in H4.
 apply H4; clear H4.
 apply env_clos_revapp; auto.
 rewrite app_length; rewrite rev_length; rewrite H2; eapply clos_after_Match2; eauto.
 apply env_ok; apply env_clos_rev; auto.
 apply env_ok; auto.
 apply env_ok; apply env_clos_revapp; auto.
 rewrite <- map_rev; apply env_ok; apply env_clos_rev; auto.
 (* nil *)
 constructor; auto.
 (* cons *)
 constructor; auto.
 apply H0; auto.
 eapply clos_after_Constr1; eauto.
 apply H2; auto.
 eapply clos_after_Constr2; eauto.
Qed.

Lemma BigStep_BigStepbis_clos : forall t v,
  clos t -> (nil |= t --> v) -> (BigStepbis t [|v|]).
Proof.
intros.
rewrite <- (do_env_subst_clos nil t); auto.
apply BigStep_BigStepbis; auto.
constructor.
red; intros; apply H; auto.
constructor.
Qed.

Lemma BigStep_subst : forall e0 t0 v0, 
  (e0|= t0 --> v0) -> 
  forall e1 e2 t n v, 
  e0 = e1++e2 -> 
  n = length e1 -> 
  t0 = t [ n:=[|v|] ] -> 
  env_clos e1 -> env_clos e2 -> val_clos v -> clos_after (S n + length e2) t ->
  exists v', 
   (e1++v::e2 |= t --> v') /\ v0~~v'.
Proof.
 set (P:=fun e0 t0 v0 => forall e1 e2 t n v, 
       e0 = e1++e2 -> 
       n = length e1 -> 
       t0 = t[n:=[|v|]] -> 
       env_clos e1 -> env_clos e2 -> val_clos v -> clos_after (S n + length e2) t ->
       exists v', (e1++v::e2 |= t --> v') /\ v0~~v').
 set (Q:=fun e0 tl0 vl0 => forall e1 e2 tl n v, 
       e0 = e1++e2 -> 
       n = length e1 -> 
       tl0 = map (subst n [|v|]) tl -> 
       env_clos e1 -> env_clos e2 -> val_clos v -> 
       (forall m, (S n + length e2) <= m -> existsb (freevar m) tl = false) ->
       exists vl', BigStep_list (e1++v::e2) tl vl' /\ 
                   map v2t vl0 = map v2t vl').
 apply (BigStep_ind2 P Q); unfold P in *; simpl; intros.
 (* Dummy *)
 clear P Q.
 destruct t; simpl in *; auto; try discriminate.
 exists VDummy; split; auto.
 destruct (lt_eq_lt_dec n0 n) as [[HH|HH]|HH]; try discriminate.
 destruct v; simpl in H1; try discriminate.
 subst.
 exists VDummy; split; auto.
 constructor.
 clear; induction e1; simpl; auto. (* lemme a part *)
 (* TVar *)
 clear P Q.
 destruct t; simpl in *; auto; try discriminate.
 destruct (lt_eq_lt_dec n1 n0) as [[HH|HH]|HH].
 inversion H2; subst.
 generalize HH H; clear; revert n1; induction e1; simpl; auto; intros.
  inversion HH.
  destruct n1; simpl in *.
  inversion H; subst; auto.
  exists v; split; auto.
  destruct (IHe1 n1); auto with arith.
  exists x; intuition.
  constructor; simpl.
  inversion H1; auto.
 destruct v0; simpl in H2; discriminate.
 inversion H2; subst.
 generalize HH H; clear; revert n1; induction e1; simpl; auto; intros.
  exists v; split; auto.
  constructor.
  destruct n1; [inversion HH | simpl in *; auto].
  destruct n1; [inversion HH | simpl in *; auto].
  destruct (IHe1 n1); auto with arith.
  assert (length e1 < n1) by omega.
  destruct n1; [inversion H0 | simpl in *; auto].
  exists x; intuition.
  constructor; simpl.
  inversion H1; auto.
 (* TFun *)
 clear P Q.
 destruct t0; simpl in *; auto; try discriminate.
 (* sous cas TFun venant d'un TVar *)
 destruct (lt_eq_lt_dec n0 n) as [[HH|HH]|HH]; try discriminate.
 destruct v; simpl in H1; try discriminate.
 inversion H1; clear H1; subst n0 n.
 exists (VClos l t0); split.
 clear; induction e1; simpl; auto. (* lemme a part *)
  constructor; simpl; auto.
  inversion IHe1; auto.
 red; simpl.
 rewrite <- subst_list_equiv.
 change (subst_list 0 (map v2t e) [|VClos l t0|] = [|VClos l t0|]).
 generalize (v2t_clos _ H4).
 rewrite subst_list_equiv.
 intros; apply subst_list_clos; auto.
 apply env_ok; subst e; apply env_clos_app; auto.
 apply env_ok; subst e; apply env_clos_app; auto.
 (* sous cas TFun venant d'un TFun *)
 inversion H1; clear H1.
 exists (VClos (e1++v::e2) t0); split; auto.
 red; simpl; f_equal.
 subst e n.
 do 2 rewrite map_app; simpl.
 rewrite <- subst_subst_list_commut3.
 rewrite <- subst_subst_list_commut3; simpl.
 rewrite map_length.
 replace (length e1 + 1) with (S (length e1)) by omega; auto.
 apply env_ok; auto.
 change (clos_list (map v2t (v::e2))).
 apply env_ok; constructor; auto.
 apply env_ok; auto.
 apply env_ok; auto.
 (* TFix *)
 clear P Q.
 destruct t0; simpl in *; auto; try discriminate.
 (* sous cas TFix venant d'un TVar *)
 destruct (lt_eq_lt_dec n0 n) as [[HH|HH]|HH]; try discriminate.
 destruct v; simpl in H1; try discriminate.
 inversion H1; clear H1; subst n0 n.
 exists (VClos_rec l t0); split.
 clear; induction e1; simpl; auto. (* lemme a part *)
  constructor; simpl; auto.
  inversion IHe1; auto.
 red; simpl.
 rewrite <- subst_list_equiv.
 change (subst_list 0 (map v2t e) [|VClos_rec l t0|] = [|VClos_rec l t0|]).
 generalize (v2t_clos _ H4).
 rewrite subst_list_equiv.
 intros; apply subst_list_clos; auto.
 apply env_ok; subst e; apply env_clos_app; auto.
 apply env_ok; subst e; apply env_clos_app; auto.
 (* sous cas TFix venant d'un TFix *)
 inversion H1; clear H1.
 exists (VClos_rec (e1++v::e2) t0); split; auto.
 red; simpl; f_equal.
 subst e n.
 do 2 rewrite map_app; simpl.
 rewrite <- subst_subst_list_commut3.
 rewrite <- subst_subst_list_commut3; simpl.
 rewrite map_length.
 replace (length e1 + 2) with (S (S (length e1))) by omega; auto.
 apply env_ok; auto.
 change (clos_list (map v2t (v::e2))).
 apply env_ok; constructor; auto.
 apply env_ok; auto.
 apply env_ok; auto.
 (* Let *) 
 clear P Q.
 destruct t; simpl in *; auto; try discriminate.
 (* sous cas TLet venant d'un TVar *)
 destruct (lt_eq_lt_dec n0 n) as [[HH|HH]|HH]; try discriminate.
 destruct v0; simpl in H1; try discriminate.
 (* sous cas TLet venant d'un TLet *)
 inversion H5; clear H5.
 destruct (H0 e1 e2 t3 n v0) as [vv1 (Hvv11,Hvv12)]; auto; clear H0.
 eapply clos_after_Let1; eauto.
 destruct (H2 (v1::e1) e2 t4 (S n) v0) as [vv0 (Hvv01,Hvv02)]; auto; clear H2.
 subst e; simpl; auto.
 simpl; auto.
 constructor; auto.
 eapply BigStep_val_clos; eauto.
 subst e; apply env_clos_app; auto.
 rewrite H4 in H9; rewrite <- app_length in H9; rewrite <- H3 in H9.
 subst t1.
 apply subst_freevar.
 subst e; rewrite app_length; omega.
 apply v2t_clos; auto.
 eapply clos_after_Let1; eauto.
 eapply clos_after_Let2; eauto.
 exists vv0; split; auto.
 econstructor; eauto.
 simpl in Hvv01.
 (* sous lemme : compatibilité de BigStep avec ~~, en particulier a droite *)
 admit.
 (* Apply *)
 clear P Q.
 destruct t0; simpl in *; auto; try discriminate.
 (* sous cas TApply venant d'un TVar *)
 destruct (lt_eq_lt_dec n0 n) as [[HH|HH]|HH]; try discriminate.
 destruct v0; simpl in H1; try discriminate.
 (* sous cas TApply venant d'un TApply *)
 inversion H7; clear H7.
 destruct (H0 e1 e2 t0_1 n v0) as [vv1 (Hvv11,Hvv12)]; auto; clear H0.
 eapply clos_after_App1; eauto.
 destruct (H2 e1 e2 t0_2 n v0) as [vv2 (Hvv21,Hvv22)]; auto; clear H2.
 eapply clos_after_App2; eauto.
 destruct vv1; red in Hvv12; simpl in Hvv12; try discriminate.
 destruct (H2 (v2::e') ???? t n v) as [vv2 (Hvv21,Hvv22)]; auto; clear H4.
 




Lemma is_var : forall t, (exists n, t = TVar n) \/ (forall n, t<>TVar n).
Proof.
 destruct t; try (right; intros; discriminate); left; exists n; auto.
Qed.

Lemma BigStepbis_BigStep : forall t0 u,  
  (BigStepbis t0 u) -> forall e t, t0 = do_env_subst e t -> 
  env_clos e -> clos_after (length e) t -> 
  exists v, (e |= t --> v) /\ [|v|] = u.
Proof.
 (*intros.
 destruct (is_var t) as [[n Hn]|Hn].
 subst t.
 case_eq (nth_error e n); intros.
 exists v; split; auto.
 unfold do_env_subst in H0; simpl in H0.
 rewrite map_length in H0; rewrite <- minus_n_O in H0.
 assert (t0 = [|v|]).
  rewrite H0.
  clear H H0 H1 H2; revert n H3; clear; induction e; destruct n; simpl; intros; try discriminate.
  inversion H3; auto.
  apply IHe; auto.
 admit. (* manque: IsValue v -> BigStepbis v u -> v=u *)
 elimtype False.
 red in H2; simpl in H2.
 generalize (H2 n).
 destruct (eq_nat_dec n n) as [_|H4]; [ |elim H4; auto].
 generalize H3; clear; revert n; induction e; simpl; intuition.
  destruct n; simpl in *.
  discriminate.
  apply (IHe n); auto with arith.
 revert t0 u H t e H0 H1 H2 Hn.*)
 set (P:=fun t0 u => forall e t, t0 = do_env_subst e t -> 
           env_clos e -> clos_after (length e) t -> (*(forall n, t<>TVar n) ->*)
          exists v, e|=t-->v /\ [|v|]=u).
 set (Q:=fun tl0 ul => forall e tl, tl0 = map (do_env_subst e) tl ->
           env_clos e -> (forall m, length e<=m-> existsb (freevar m) tl = false) ->
           (*(forall n t, In t tl -> t<>TVar n) ->*)
           exists vl, BigStep_list e tl vl /\ map v2t vl = ul).
 apply (BigStepbis_ind2 P Q); unfold do_env_subst in *; red; simpl; intros.

 (* TDummy *)
 destruct t; simpl in *; auto; try discriminate.
 exists VDummy; split; auto.
 (* partie commune pour var *)
 rewrite map_length in H; rewrite <- minus_n_O in H.
 case_eq (nth_error e n); intros.
 exists v; split; auto.
 rewrite H.
 revert H2; clear; revert n; induction e; destruct n; simpl; intros; try discriminate.
 inversion H2; auto.
 apply IHe; auto.
 elimtype False.
 red in H1; simpl in H1.
 generalize (H1 n).
 destruct (eq_nat_dec n n) as [_|HH]; [ |elim HH; auto].
 generalize H2; clear; revert n; induction e; simpl; intuition.
  destruct n; simpl in *.
  discriminate.
  apply (IHe n); auto with arith.
 (* fin partie commune *)

 (* TFun *)
 destruct t0; simpl in *; auto; try discriminate.
 (* partie commune pour var *)
 rewrite map_length in H; rewrite <- minus_n_O in H.
 case_eq (nth_error e n); intros.
 exists v; split; auto.
 rewrite H.
 revert H2; clear; revert n; induction e; destruct n; simpl; intros; try discriminate.
 inversion H2; auto.
 apply IHe; auto.
 elimtype False.
 red in H1; simpl in H1.
 generalize (H1 n).
 destruct (eq_nat_dec n n) as [_|HH]; [ |elim HH; auto].
 generalize H2; clear; revert n; induction e; simpl; intuition.
  destruct n; simpl in *.
  discriminate.
  apply (IHe n); auto with arith.
 (* fin partie commune *)
 inversion H; clear H.
 exists (VClos e t0); split; simpl; auto.
 rewrite subst_list_equiv; auto.

 (* TFix *)
 destruct t0; simpl in *; auto; try discriminate.
 (* partie commune pour var *)
 rewrite map_length in H; rewrite <- minus_n_O in H.
 case_eq (nth_error e n); intros.
 exists v; split; auto.
 rewrite H.
 revert H2; clear; revert n; induction e; destruct n; simpl; intros; try discriminate.
 inversion H2; auto.
 apply IHe; auto.
 elimtype False.
 red in H1; simpl in H1.
 generalize (H1 n).
 destruct (eq_nat_dec n n) as [_|HH]; [ |elim HH; auto].
 generalize H2; clear; revert n; induction e; simpl; intuition.
  destruct n; simpl in *.
  discriminate.
  apply (IHe n); auto with arith.
 (* fin partie commune *)
 inversion H; clear H.
 exists (VClos_rec e t0); split; simpl; auto.
 rewrite subst_list_equiv; auto.

 (* TLet *)
 destruct t; simpl in *; auto; try discriminate.
 (* partie commune pour var *)
 rewrite map_length in H3; rewrite <- minus_n_O in H3.
 admit. (*le nth donne soit un TVar soit un IsValue, mais pas de TLet *)
 (* fin partie commune *)
 inversion H3; clear H3.
 unfold P in *.
 destruct (H2 e t4[0:=v1]) as (vv,(Hvv1,Hvv2)); auto; clear H2.
 rewrite subst_list_equiv; auto.
 rewrite <- subst_subst_list_commut.
 rewrite H8; rewrite subst_list_equiv; auto.
 admit. (* BigStepbis preserve la cloture de t1 *)
 apply env_ok; auto.
 apply subst_freevar; auto with arith.
 admit.
 eapply clos_after_Let2; eauto.
 destruct (H0 e t3) as (vv1,(Hvv11,Hvv12)); auto; clear H0.
 eapply clos_after_Let1; eauto.
 exists vv; split; auto.
 econstructor; eauto.
 admit. (* Lemma de substitution nécessaire ... *)


 (* App *)
 
 (* Appr *)

 (* Constr *)

 (* Iota *)

Qed. 



(*Lemma compat2 : forall t v, (t1 ==> [|v|]) -> exists v', v~~v' /\ 
 nil |= t1 --> v'. 
*)


Lemma compat2 : forall t1 t2, t1 --> t2 ->
  forall v v' e, (e |= t1 --> v) -> (e |= t2 --> v') -> v~~v'.
Proof.
  induction 1.


  intros.
  inversion_clear H.
  inversion H1; subst; clear H1.


  induction t1; intros.
    simpl.
    inversion H0; subst.
    inversion H3; subst.
    inversion H7; subst.
    auto.
    inversion H3.
    
    simpl.
    destruct (lt_eq_lt_dec n 0).
      destruct s.
      inversion l.
      subst.
      inversion H0; subst.
        inversion H3; subst.
        inversion H7; subst.
        simpl in H4; inversion H4; subst.
        auto.
        inversion H3.
      inversion H0; subst.
        inversion H3; subst.
        inversion H7; subst.
        clear - H4 l.
        constructor.
        destruct n.
          inversion l.
          simpl in *.
          auto.
        inversion H3.
    
    simpl.
    inversion H0; subst.
    inversion H3; subst.
to.



        inversion H7; subst.

to.
        inversion H3.



  induction t1; intros.

  inversion H.

  inversion H.

  inversion H.
  subst.




  induction 2; intros.

  inversion_clear H.
  inversion H0.
  subst.


Lemma compat1 : forall t1 t2, t1 --> t2 ->
  forall v e, Vdata v -> e |= t1 --> v -> e |= t2 --> v.
Proof.
  induction 1.

  induction t1; intros.
    simpl.
    inversion H0; subst.
    inversion H3; subst.
    inversion H7; subst.
    auto.
    inversion H3.
    
    simpl.
    destruct (lt_eq_lt_dec n 0).
      destruct s.
      inversion l.
      subst.
      inversion H0; subst.
        inversion H3; subst.
        inversion H7; subst.
        simpl in H4; inversion H4; subst.
        auto.
        inversion H3.
      inversion H0; subst.
        inversion H3; subst.
        inversion H7; subst.
        clear - H4 l.
        constructor.
        destruct n.
          inversion l.
          simpl in *.
          auto.
        inversion H3.
    
    simpl.
    inversion H0; subst.
    inversion H3; subst.
to.



        inversion H7; subst.

to.
        inversion H3.



  induction t1; intros.

  inversion H.

  inversion H.

  inversion H.
  subst.




  induction 2; intros.

  inversion_clear H.
  inversion H0.
  subst.
*)



(*
Lemma subst_correct : forall t1 t2,
  SmallStep t1 t2 -> forall n t, SmallStep (subst n t t1) (subst n t t2).
Proof.
  induction 1; intros.

  simpl.
  induction t1.
  simpl.
  econstructor.




  stop. (* début preuve 1 *)
  induction t1; intros.

  simpl.
  inversion_clear H.

  simpl.
  destruct (eq_nat_dec n n0).
  inversion H.
  inversion H.

  simpl.
  inversion H.
  subst t0 t1.
  rewrite H0.
  stop. (* fin preuve 1 *)


  apply SS_zeta.

  apply SS_let1.

  econstructor.

  inversion_clear H.




Lemma subst_env_correct : forall e t v,
  BigStep e t v -> BigStep nil (subst_env 0 e t) v.
Proof.
  induction 1.
  rewrite (subst_env_TDummy e 0); auto.

  induction e; simpl.
  auto.
  simpl in H.

  apply (BigStep_V

  destruct e; simpl; auto.



(*
Lemma SS_compat1 : forall t v e,
  BigStep e t v -> SmallStep_lax (subst_env 0 e t) (v2t v).
Proof.
  induction t; intros.
  (* TDummy *)
  inversion_clear H.
  left.
  rewrite (subst_env_TDummy e 0).
  simpl; auto.
  (* TVar *)
  inversion_clear H.
  induction e.
  destruct n; simpl in H0; inversion H0.
*)


Theorem SS_complete : forall t1 t2 v1 v2,
  SmallStep t1 t2 -> BigStep nil t1 v1 -> BigStep nil t2 v2 -> v1 = v2.
Proof.
  induction 1; intros.




Theorem SS_compat : forall e t1 t2 v,
  BigStep e t1 v -> SmallStep (subst_env 0 e t1) (subst_env 0 e t2) -> BigStep e t2 v.
Proof.
  induction t1; intros.
  (* TDummy *)

  inversion_clear H.
  induction e.
  simpl in H0.
  inversion H0; auto.
  simpl in H0.



  subst.

  destruct e; simpl in H0; auto.
  inversion H; inversion H0; subst.
  inversion H.
*)





(***** Définitions pour preuves de programmes extraits *****)

Fixpoint internalize_nat n := match n with
  | O => TConstr 0 nil
  | S n => TConstr 1 (internalize_nat n :: nil)
end.

Coercion internalize_nat : nat >-> term.

Lemma intern_clos : forall (n : nat), clos n.
Proof.
  unfold clos.
  induction n; intros.
  simpl; auto.
  simpl; f_equal; f_equal; auto.
Qed.

Hint Resolve intern_clos.

(***** Preuve de plus *****)

Internal Extraction plus.

Lemma l1 : forall n,
  plus__extr @ 0 @ n ==> n.
Proof.
unfold plus__extr.
econstructor.
eapply SS_app1.
eapply SS_iota2.
simpl.
econstructor.
eapply SS_beta.
simpl.
econstructor.
eapply SS_iota1.
simpl.
auto.
auto.
(*simpl.
econstructor.
*)Qed.


Lemma l2 : forall n m,
  clos n -> clos m ->
  SmallSteps
    (plus__extr @ (TConstr 1 (n::nil)) @ m)
    (TConstr 1 (plus__extr @ n @ m :: nil)).
Proof.
unfold plus__extr.
econstructor.
eapply SS_app1.
eapply SS_iota2.
set (f :=
(TFix
        (TFun
           (TMatch (TVar 1)
              (Patc 0 (TVar 0)
               :: Patc 1 (TConstr 1 ((TVar 3 @ TVar 0) @ TVar 1 :: nil))
                  :: nil))))).

simpl.
rewrite H.
econstructor.
eapply SS_beta.
simpl.
econstructor.
eapply SS_iota1.
simpl.
auto.
simpl.
auto.
rewrite H.
simpl.
rewrite H0.
unfold f.
apply SmallSteps_refl.
Qed.

Lemma l3 : forall (n m : nat),
  SmallSteps (plus__extr @ n @ m) (n+m).
Proof.
induction n.
simpl.
intros.
apply l1.
intros.
simpl.
eapply SmallSteps_trans2.
eapply l2; auto.
assert (H := IHn m).
clear IHn.
induction H.
econstructor.
econstructor.
eapply SS_constr.
econstructor.
eauto.
eauto.
Qed.

(***** pred *****)

Print pred.
Internal Extraction pred.

Lemma l4 : forall (n:nat),
  pred__extr @ n ==> pred n.
Proof.
unfold pred__extr.
econstructor.
constructor.
simpl.
destruct n; simpl.
apply SS_is_SmallSteps.
refine (SS_iota1 0 nil _ _ _).
simpl; auto.
simpl; auto.
apply SS_is_SmallSteps.
exact (SS_iota1 1 ((n:term) :: nil)
           (Patc 0 (TConstr 0 nil) :: Patc 1 (TVar 0) :: nil) (TVar 0)
           (refl_equal (Some (Patc 1 (TVar 0))))).
Qed.

Implicit Arguments SS_is_SmallSteps.
Implicit Arguments SmallSteps_trans.
Implicit Arguments SS_beta.

Print l4.



Fixpoint test n :=
  match n with
    | O => O
    | S n => test n
  end.

Internal Extraction test.

Lemma l5 : forall (n:nat),
  test__extr @ n ==> test n.
Proof.
fix 1.
unfold test__extr.
econstructor.
constructor.
simpl.
rewrite (intern_clos n).
destruct n.
simpl.
apply SS_is_SmallSteps.
refine (SS_iota1 0 nil _ _ _); simpl; auto.
simpl.
econstructor.
eapply SS_iota1.
simpl; auto.
simpl; auto.
(*simpl; auto.*)
Qed.

Print eq_ind_r.

Print l5.


stop.

