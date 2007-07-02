Require Import List Arith Max Omega Bool Setoid Wf_nat.

Hint Extern 1 (?f _ = ?f _) => f_equal.
Hint Extern 1 (?f _ _ = ?f _ _) => f_equal.
Hint Extern 1 (?f _ _ _ = ?f _ _ _) => f_equal.


Ltac dec := 
  let H := fresh "H" in 
  destruct lt_eq_lt_dec as [[H|H]|H] ||
  destruct le_lt_dec as [H|H] || 
  destruct eq_nat_dec as [H|H] || fail; 
  simpl; 
  trivial; 
  try (intros; discriminate); 
  try (elimtype False; omega);
  match goal with 
    | H:?n=?n  |- _ => clear H
    | H:?n<=?n |- _ => clear H
    | _ => idtac
  end.

Ltac inv_clear H := inversion H; try clear H; subst.


(** *  Sommaire des notations semantiques: *)

(** Bigstep avec environnement: *) 
Reserved Notation      "e |= t --> v"      (at level 100, t at next level).
(** Un pas de smallstep *)
Reserved Notation      "t --> u"           (at level 100).  
(** Zero, un ou plusieurs pas de smallstep *)
Reserved Notation      "t ==> u"           (at level 100).
(** n pas de smallstep *)
Reserved Notation      "t ==[ n ]=> u "    (at level 100, n at next level).



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

(** Listes de termes clos *)

Inductive clos_list : list term -> Prop := 
 | clos_list_nil : clos_list nil
 | clos_list_cons : forall a l, clos a -> clos_list l -> clos_list (a::l).
Hint Constructors clos_list.

(** termes clos au dela d'un certain indice *)

Definition clos_after n t := forall m, n<=m -> freevar m t = false. 

Fixpoint clos_after' n t { struct t } := match t with 
 | TDummy => True
 | TVar k => k < n 
 | TFun t => clos_after' (S n) t
 | t1@t2 => clos_after' n t1 /\ clos_after' n t2
end.

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

(** Une valeur peut etre vue en tant que terme *)

Fixpoint v2t v := match v with
 | VDummy => TDummy
 | VClos e f => TFun (subst_list_iter 1 (map v2t e) f)
end.





(** Resultats concernant termes, cloture et substitutions. *)

Lemma clos_alt : forall t, clos t <-> clos_after 0 t.
Proof.
 unfold clos, clos_after; intuition.
Qed.

Lemma clos_after_alt : 
 forall t n, clos_after n t <-> clos_after' n t.
Proof.
 induction t; unfold clos_after in *; simpl; intros.
 intuition.
 split; intros; try dec.
 destruct (le_lt_dec n0 n) as [H'|H']; auto.
 generalize (H _ H'); dec.
 rewrite <- IHt.
 intuition; simpl.
 replace m with (S (pred m)) by omega.
 apply H; omega.
 rewrite <- IHt1; rewrite <- IHt2.
 intuition; simpl; destruct (orb_false_elim _ _ (H _ H0)); auto.
Qed. 

Ltac simpl_clos_after := repeat rewrite clos_after_alt in *; 
 simpl in *; repeat rewrite <- clos_after_alt in *.

Lemma clos_list_alt : forall l, clos_list l <-> forall u, In u l -> clos u.
Proof.
 induction l; split; simpl; auto.
 inversion 2.
 inversion_clear 1.
 inversion_clear 1; subst; auto.
 rewrite IHl in H1; auto.
 constructor; auto.
 rewrite IHl; auto.
Qed. 

Lemma clos_list_cons_iff : forall a l, clos_list (a::l) <-> clos a /\ clos_list l.
Proof.
 split; inversion 1; auto.
Qed.

Lemma clos_list_app_iff : forall l l', 
 clos_list (l++l') <-> clos_list l /\ clos_list l'.
Proof.
 induction l; simpl; auto.
 intuition.
 intros; do 2 rewrite clos_list_cons_iff.
 rewrite IHl; intuition.
Qed.

Lemma subst_clos_after_iff : forall t n, 
   clos_after n t <-> (forall n0 t0, n <= n0 -> subst n0 t0 t = t).
Proof.
 induction t; simpl; intros; simpl_clos_after.
 (* Dummy *)
 intuition.
 (* Var *)
 intuition; try dec.
 destruct (le_lt_dec n0 n) as [H'|H']; auto.
 generalize (H n TDummy H'); dec.
 (* Fun *)
 rewrite IHt; intuition.
 replace n0 with (S (pred n0)) by omega.
 assert (n <= pred n0) by omega.
 generalize (H _ t0 H1); inversion 1; auto.
 (* Apply *)
 rewrite IHt1; rewrite IHt2.
 intuition.
 generalize (H _ t0 H0); inversion 1; auto.
 generalize (H _ t0 H0); inversion 1; auto.
Qed.

Lemma subst_clos_iff : forall t, clos t <-> (forall n u, t[n:=u] = t).
Proof.
 intros; rewrite clos_alt; rewrite subst_clos_after_iff; intuition.
Qed.

Lemma subst_clos : forall t, clos t -> forall n u, t[n:=u] = t.
Proof.
 intros t H n u; rewrite subst_clos_iff in H; rewrite H; auto.
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

Lemma subst_clos_after : forall t n u m, n <= m -> 
  clos u -> clos_after (S m) t -> clos_after m (t[n:=u]).
Proof.
induction t; simpl; intros; simpl_clos_after; auto with arith.
dec.
simpl_clos_after; omega.
red in H0; red; auto.
simpl_clos_after; omega.
intuition.
Qed.

Lemma subst_list_iter_clos_after : forall l n t, 
  clos_list l -> 
  clos_after (n+length l) t -> 
  clos_after n (t[n;;=l]).
Proof.
induction l; simpl; auto; intros.
replace n with (n+0); auto with arith.
inv_clear H.
apply IHl; auto.
apply subst_clos_after; auto with arith.
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
inv_clear H.
assert (IH:=fun t n => IHl t n H3); clear IHl H3.
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
repeat dec; auto.
Qed.

Hint Resolve subst_commut.

Lemma subst_list_iter_commut : forall l t u n, 
 clos u -> clos_list l -> 
 t[S n;;=l][n:=u] = t[n:=u][n;;=l].
Proof.
induction l; simpl; auto; intros.
inv_clear H0.
rewrite IHl; auto.
Qed.
Hint Resolve subst_list_iter_commut.







(** * (1) Semantique big-step avec environnement : *)

(**  Le predicat d'evaluation d'un terme dans un environnement (liste de valeurs) *)

Inductive BigStep : list value -> term -> value -> Prop:=
  | BigStep_Dum : forall e,  
     (e |= TDummy --> VDummy)
  | BigStep_Var : forall n e v, nth_error e n = Some v -> 
     (e |= TVar n --> v)
  | BigStep_Fun : forall e t, 
     (e |= TFun t --> VClos e t)
  | BigStep_App : forall e e' t t1 t2 v v2,
     (e |= t1-->VClos e' t) -> 
     (e |= t2-->v2) -> 
     (v2::e'|=t-->v) -> 
     (e |= t1@t2-->v)
where "e |= t --> v" := (BigStep e t v).

Hint Constructors BigStep.


(** * (2) Semantique small-step completement sans environnement *)

Inductive IsValue : term -> Prop := 
  | IsValue_Dummy : IsValue TDummy 
  | IsValue_Fun : forall t, IsValue (TFun t).

Inductive SmallStep : term -> term -> Prop :=
  | SmallStep_beta : forall t1 t2, IsValue t2 -> 
    ((TFun t1)@t2 --> t1[0:=t2])
  | SmallStep_app1 : forall u v t, (u-->v) -> (u@t-->v@t)
  | SmallStep_app2 : forall u v t, (u-->v) -> (t@u-->t@v)
where "t --> u" := (SmallStep t u).

Fixpoint SmallStepN n := match n with 
  | O => fun t r => t=r
  | S n => fun t r => exists s, (t-->s) /\ (s ==[n]=> r)
 end
where "t ==[ n ]=> u" := (SmallStepN n t u).

Definition SmallSteps t u := exists n, (t==[n]=>u).
Notation " t ==> u" := (SmallSteps t u).

Hint Constructors IsValue SmallStep.




Lemma IsValue_v2t : forall v, IsValue (v2t v).
Proof.
 induction v; simpl; auto.
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

Lemma v2t_clos : forall v, val_clos v -> clos (v2t v). (* RECIPROQUE FAUSSE ! *)
Proof.
 apply (val_clos_ind2 
         (fun v => clos (v2t v)) 
         (fun e => forall t, In t (map v2t e) -> clos t)); 
 simpl; auto; intros.
 
 red; simpl; auto.

 red; intros; simpl.
 apply subst_list_iter_clos_after; auto with arith.
 rewrite clos_list_alt; intros.
 apply H0; auto.
 rewrite map_length; auto.

 contradiction.
 
 intuition.
 subst t; auto.
Qed.
Hint Resolve v2t_clos.

Lemma v2t_env_clos: forall e, env_clos e -> clos_list (map v2t e). (* RECIPROQUE FAUSSE *)
Proof.
induction e; simpl; auto.
inversion_clear 1; constructor; auto.
Qed.
Hint Resolve v2t_env_clos.


(* Proprietes globales de SmallSteps *)

Lemma SmallSteps_trans : forall t u r,
  (t-->u) -> (u==>r) -> (t==>r).
Proof.
  intros t u r H (n,H'); exists (S n); simpl; firstorder.
Qed.

Lemma SmallSteps_trans2 : forall t u r,
  (t==>u) -> (u==>r) -> (t==>r).
Proof.
  intros t u r (n,H) (n',H'); exists (n+n'); revert t H.
  induction n; simpl; auto; firstorder; congruence.
Qed.

Lemma SmallSteps_app1 : 
 forall t u r, (t==>u) -> (t@r ==> u@r).
Proof.
 intros t u r (n,H); exists n; revert t H.
 induction n; simpl; try congruence.
 intros t (s,(H,H')); exists (s@r); auto.
Qed.

Lemma SmallSteps_app2 : 
 forall t u r, (t==>u) -> (r@t ==> r@u).
Proof.
 intros t u r (n,H); exists n; revert t H.
 induction n; simpl; try congruence.
 intros t (s,(H,H')); exists (r@s); auto.
Qed.

(* Reductions et cloture: *)

Lemma BigStep_val_clos : forall e t v, env_clos e -> clos_after (length e) t -> 
 (e|=t-->v) -> val_clos v.
Proof.
induction 3; simpl; intros; simpl_clos_after; auto.
revert n H1 H0; induction e.
 inversion 2.
 inversion_clear H.
 destruct n; simpl; eauto with arith.
 inversion 1; subst; auto.
destruct H0.
assert (val_clos (VClos e' t)) by auto.
inversion_clear H2; auto.
Qed.

Lemma SmallStep_clos : forall t u, (t-->u) -> clos t -> clos u.
Proof.
induction 1.
repeat rewrite clos_alt; simpl_clos_after.
destruct 1.
apply subst_clos_after; auto.
rewrite clos_alt; auto.
revert IHSmallStep; repeat rewrite clos_alt; simpl_clos_after; intuition.
revert IHSmallStep; repeat rewrite clos_alt; simpl_clos_after; intuition.
Qed.
Hint Resolve SmallStep_clos.

Lemma SmallStepN_clos : forall n t u, (t==[n]=>u) -> clos t -> clos u.
Proof.
induction n; simpl in *; intuition.
subst; auto.
destruct H as (s,(A,b)).
eauto.
Qed.


(* Le lemme crucial pour le sens dur de l'equivalence ((2)->(1)) : 
   inversion de la reduction d'une application *)

Lemma SmallStepN_inv_app : forall n t u r, IsValue r -> 
(t@u ==[n]=> r) -> 
exists t', exists r', exists n1, exists n2, exists n3, 
  S (n1+n2+n3) = n /\ 
  IsValue r' /\
  (u ==[n1]=> r') /\
  (t ==[n2]=> TFun t')  /\
  (t'[0:=r'] ==[n3]=> r).
Proof.
induction n; simpl; intros.
subst r; inversion H.

destruct H0 as (s,(Hs1,Hs2)).
inv_clear Hs1.

exists t1; exists u; exists 0; exists 0; exists n.
repeat split; simpl; auto.

rename v into t'.
destruct (IHn _ _ _ H Hs2) as (t1,(u1,(n1,(n2,(n3,(A,(B,(C,(D,E))))))))); clear IHn.
exists t1; exists u1; exists n1; exists (S n2); exists n3.
repeat split; simpl; auto; destruct A; auto.
omega.
exists t'; auto.

rename v into u'.
destruct (IHn _ _ _ H Hs2) as (t1,(u1,(n1,(n2,(n3,(A,(B,(C,(D,E))))))))); clear IHn.
exists t1; exists u1; exists (S n1); exists n2; exists n3.
repeat split; simpl; auto; destruct A; auto.
exists u'; auto.
Qed.

(** (1) -> (2) *)

Lemma BigStep_SmallSteps : forall e t v, 
 env_clos e -> clos_after (length e) t -> 
 (e|=t-->v) -> (t[0::=map v2t e] ==> v2t v).
Proof.
 induction 3; simpl; intros; simpl_clos_after; auto.
 exists 0; simpl; auto.
 exists 0; simpl; auto.
  replace (n-0) with n by omega.
  revert n H1 H0; induction e.
   inversion 2.
   destruct n; simpl in *; intros.
   inv_clear H1; auto.
   inv_clear H.
   apply IHe; auto with arith.
 exists 0; simpl; auto.
  rewrite subst_list_equiv; auto.
 destruct H0; simpl.
 apply SmallSteps_trans2 with (v2t (VClos e' t) @ t2 [0::=map v2t e]).
 apply SmallSteps_app1; auto.
 apply SmallSteps_trans2 with (v2t (VClos e' t) @ v2t v2).
 apply SmallSteps_app2; auto.
 simpl.
 eapply SmallSteps_trans; eauto.
 assert (H3:=BigStep_val_clos _ _ _ H H0 H1_).
 inversion_clear H3.
 assert (H3:=BigStep_val_clos _ _ _ H H1 H1_0).
 rewrite subst_list_iter_commut; auto.
 change (t[0;;=map v2t (v2::e')] ==> v2t v).
 rewrite subst_list_equiv; auto.
 Qed. 


(** (2) -> (1) *)

Lemma SmallSteps_BigStep : forall e t u,  
 env_clos e -> clos_after (length e) t -> IsValue u -> 
 (t[0::=map v2t e] ==> u) -> 
 exists v, (e|=t-->v) /\ v2t v = u /\ val_clos v.
Proof.
intros e t u H H0 H1 (n,H2); revert e t u H H0 H1 H2.
induction n using lt_wf_ind; intros.
destruct t; simpl in *; simpl_clos_after.
(* Dummy *)
exists VDummy; split; [ | split ]; simpl; auto.
destruct n; simpl in *; auto.
destruct H3 as (s,(Hs1,_)); inversion Hs1.
(* Var *)
rename n0 into k.
replace (k-0) with k in H3 by omega.
assert (exists v, val_clos v /\ nth_error e k = Some v /\ 
                  nth k (map v2t e) (TVar (k - length (map v2t e))) = v2t v).
 clear - H1 H0; revert k H1 H0; induction e; simpl in *.
 inversion 1.
 destruct k.
 exists a; auto.
 inversion_clear H0; split; auto.
 intros; inversion_clear H0; 
  destruct (IHe k) as (v,(A,B)); auto with arith.
 exists v; auto.
destruct H4 as (v,(Hv1,(Hv2,Hv3))); rewrite Hv3 in H3; clear Hv3.
exists v; split; [ | split ]; eauto.
destruct n; simpl in *; auto.
destruct H3 as (s,(Hs1,_)); destruct v; simpl; inversion Hs1.
(* Fun *)
exists (VClos e t); split; [ | split ]; auto.
destruct n; simpl in *; auto.
rewrite subst_list_equiv; auto.
destruct H3 as (s,(Hs1,_)); inversion Hs1.
(* Apply *)
destruct H1.
destruct (SmallStepN_inv_app _ _ _ _ H2 H3) as 
 (t',(u',(n1,(n2,(n3,(A,(B,(C,(D,E))))))))).
assert (n1<n) by omega.
assert (n2<n) by omega.
assert (n3<n) by omega.
destruct (H n1 H5 e t2 u') as (v',(Av',(Bv',Cv'))); auto.
destruct (H n2 H6 e t1 (TFun t')) as (v0,(Av0,(Bv0,Cv0))); auto.
destruct v0; simpl in *; try discriminate.
inversion_clear Cv0.
inversion Bv0; clear Bv0; subst t'.
rewrite subst_list_iter_commut in E; auto.
subst u'.
change (t [0;;=map v2t (v'::l)] ==[n3]=>u) in E.
destruct (H n3 H7 (v'::l) t u) as (v,(Av,(Bv,Cv))); auto.
rewrite <- subst_list_equiv; auto.
exists v; eauto.
apply (SmallStepN_clos _ _ _ C).
rewrite clos_alt.
rewrite <- subst_list_equiv; auto.
apply subst_list_iter_clos_after; simpl; auto.
rewrite map_length; auto.
Qed.


(* La meme equivalence, specialisee aux termes clos. *)

(* (1)->(2) *)

Lemma BigStep_SmallSteps_clos : forall t v, clos t -> 
 (nil|=t-->v) -> (t ==> v2t v).
Proof.
intros.
replace t with (t[0::=map v2t nil]).
apply BigStep_SmallSteps; simpl; auto.
rewrite <- clos_alt; auto.
rewrite <- subst_list_equiv; auto.
Qed.


Lemma SmallSteps_BigStep_clos : forall t u, clos t -> IsValue u -> 
 (t==>u) -> exists v, (nil|=t-->v) /\ v2t v = u /\ val_clos v.
Proof.
intros.
apply SmallSteps_BigStep; simpl; auto.
rewrite <- clos_alt; auto.
rewrite <- subst_list_equiv; auto.
Qed.

(* NB: (IsValue u) implique l'existence d'un v' tel que (v2t v' = t)
   mais rien n'oblige v et v' a coincider. Ils sont juste equivalents 
   au sens ou v2t v = v2t v'. 
*) 

