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

Lemma map_id : forall (A:Type)(f:A->A)(l:list A), 
 map f l = l <-> forall a, In a l -> f a = a.
Proof.
 induction l; simpl; intuition; injection H1; auto; congruence.
Qed.

Lemma map_ext_iff : forall (A B : Type) (f g : A -> B)(l:list A),
 (map f l = map g l) <-> (forall a, In a l -> f a = g a).
Proof.
 induction l; simpl; intuition; injection H1; auto; congruence.
Qed.


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

Inductive term : Set :=
  | TDummy : term
  | TVar : nat -> term
  | TLet : term -> term -> term
  | TFun : term -> term
  | TFix : term -> term
  | TApply : term -> term -> term
  | TConstr : nat -> list term -> term
  | TMatch : term -> list pat -> term
with pat : Set :=
  | Patc : nat -> term -> pat
.

Notation "a @ b" := (TApply a b) (at level 40).

Definition fstpat (p:pat) := let (k,_):=p in k.
Definition sndpat (p:pat) := let (_,t):=p in t.

(** Les valeurs possibles apres evaluation : constantes ou clotures *)

Inductive value : Set:=
  | VDummy : value
  | VClos : list value -> term -> value
  | VClos_rec : list value -> term -> value
  | VConstr : nat -> list value -> value
.

(** principes d'induction correctes. *)

Section correct_term_ind. 

Variables 
 (P : term -> Prop)
 (Pl : list term -> Prop) 
 (Pp : pat -> Prop) 
 (Ppl : list pat -> Prop). 

Hypothesis 
 (Hdummy : P TDummy)
 (Hvar : forall k, P (TVar k))
 (Hlet : forall t1, P t1 -> forall t2, P t2 -> P (TLet t1 t2))
 (Hfun : forall t, P t -> P (TFun t))
 (Hfix : forall t, P t -> P (TFix t))
 (Happ : forall t1, P t1 -> forall t2, P t2 -> P (TApply t1 t2)) 
 (Hcnstr : forall k tl, Pl tl -> P (TConstr k tl))
 (Hmtch : forall t, P t -> forall pl, Ppl pl -> P (TMatch t pl))
 (Hnil : Pl nil) 
 (Hcons : forall t, P t -> forall tl, Pl tl ->Pl (t::tl)) 
 (Hpnil : Ppl nil)
 (Hpcons : forall p, Pp p -> forall pl, Ppl pl -> Ppl (p::pl))
 (Hpat : forall k t, P t -> Pp (Patc k t)). 

Fixpoint term_ind2 t : P t := match t as x return P x with 
  | TDummy => Hdummy 
  | TVar k => Hvar k
  | TLet t1 t2 => Hlet  t1 (term_ind2 t1) t2 (term_ind2 t2) 
  | TFun t => Hfun t (term_ind2 t)
  | TFix t => Hfix t (term_ind2 t) 
  | t1@t2 => Happ  t1 (term_ind2 t1) t2 (term_ind2 t2) 
  | TConstr k tl => Hcnstr k tl 
    ((fix list_ind (l:list term) : Pl l := match l as x return Pl x with 
       | nil => Hnil 
       | cons t l => Hcons t (term_ind2 t) l (list_ind l)
      end) tl)
  | TMatch t pl => Hmtch t (term_ind2 t) pl 
    ((fix listpat_ind (l:list pat) : Ppl l := match l as x return Ppl x with 
       | nil => Hpnil 
       | cons p l => Hpcons p (pat_ind2 p) l (listpat_ind l)
      end) pl)
  end 
with pat_ind2 (p : pat) : Pp p := match p as x return Pp x with 
 | Patc k t => Hpat k t (term_ind2 t) 
end.

End correct_term_ind. 

Section correct_value_ind. 

Variables 
 (P : value -> Prop)
 (Pl : list value -> Prop).

Hypothesis 
 (Hdummy : P VDummy)
 (Hclos : forall e t, P (VClos e t))
 (Hclos_rec : forall e t, P (VClos_rec e t))
 (Hcnstr : forall k vl, Pl vl -> P (VConstr k vl))
 (Hnil : Pl nil)
 (Hcons : forall v, P v -> forall vl, Pl vl ->Pl (v::vl)).

Fixpoint value_ind2 v : P v := match v as x return P x with 
  | VDummy => Hdummy 
  | VClos e n => Hclos e n
  | VClos_rec e n => Hclos_rec e n 
  | VConstr k vl => Hcnstr k vl 
    ((fix list_ind (l:list value) : Pl l := match l as x return Pl x with 
       | nil => Hnil 
       | cons v l => Hcons v (value_ind2 v) l (list_ind l)
      end) vl)
  end.

End correct_value_ind. 

(** deux cas particuliers de term_ind2 *)

Definition term_ind2_zero (P: term->Prop) := 
 term_ind2 P 
  (fun l => forall t, In t l -> P t)
  (fun p => P (sndpat p))
  (fun pl => forall p, In p pl -> P (sndpat p)).

Definition term_ind2_one (P: term->nat->Prop) := 
 term_ind2 (fun t => forall n, P t n)
  (fun l => forall n t, In t l -> P t n)
  (fun p => forall n, P (sndpat p) ((fstpat p)+n))
  (fun pl => forall n p, In p pl -> P (sndpat p) ((fstpat p)+n)).

(** Variables libres *)

(** Est-ce que n est libre dans t ? *)

Fixpoint freevar (n:nat)(t:term) { struct t } : bool := 
 match t with 
    | TDummy => false
    | TVar k => if eq_nat_dec k n then true else false
    | TFun t => freevar (S n) t
    | TFix t => freevar (S (S n)) t
    | TLet t1 t2 => (freevar n t1) || (freevar (S n) t2)
    | t1@t2 => (freevar n t1) || (freevar n t2)
    | TConstr k tl => existsb (freevar n) tl
    | TMatch t pl => (freevar n t) || 
         existsb (fun (p:pat) => let (k,t) := p in freevar (k+n) t) pl
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

Definition clos_after' n t := match t with 
 | TDummy => True
 | TVar k => k < n 
 | TFun t => clos_after (S n) t
 | TFix t => clos_after (S (S n)) t
 | TLet t1 t2 => clos_after n t1 /\ clos_after (S n) t2
 | t1@t2 => clos_after n t1 /\ clos_after n t2
 | TConstr k tl => forall u, In u tl -> clos_after n u
 | TMatch t pl => clos_after n t /\ 
        forall p, In p pl -> let (k,t) := p in clos_after (k+n) t
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
    | TFix t => TFix (subst (S (S n)) u t)
    | TLet t1 t2 => TLet (subst n u t1) (subst (S n) u t2)
    | t1@t2 => (subst n u t1)@(subst n u t2)
    | TConstr k tl => TConstr k (map (subst n u) tl)
    | TMatch t pl => 
        TMatch (subst n u t) 
          (map (fun p:pat => let (k,t):=p in Patc k (subst (k+n) u t)) pl)
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
   | TFix t => TFix (subst_list (S (S n)) l t)
   | t1@t2 => (subst_list n l t1)@(subst_list n l t2)
   | TLet t1 t2 => TLet (subst_list n l t1) (subst_list (S n) l t2)
   | TConstr k tl => TConstr k (map (subst_list n l) tl)
   | TMatch t pl => TMatch (subst_list n l t)
         (map (fun p:pat => let (k,t):=p in Patc k (subst_list (k+n) l t)) pl)
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
 | VClos_rec e f => TFix (subst_list_iter 2 (map v2t e) f)
 | VConstr i vl => TConstr i (map v2t vl)
end.





(** Resultats concernant termes, cloture et substitutions. *)

Lemma clos_alt : forall t, clos t <-> clos_after 0 t.
Proof.
 unfold clos, clos_after; intuition.
Qed.

Lemma existsb_forall : forall (A:Type)(f:A->bool)(l:list A), 
 existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
induction l; intuition.
inversion H0.
simpl in *; inversion_clear H2; subst; auto; 
 destruct (orb_false_elim _ _ H1); auto.
simpl.
rewrite (H1 a); simpl; auto.
apply H0; intros.
apply H1; simpl; auto.
Qed.

Lemma clos_after_alt : 
 forall t n, clos_after n t <-> clos_after' n t.
Proof.
 destruct t; simpl; unfold clos_after in *; simpl; intros.
 intuition.
 split; intros; try dec.
 destruct (le_lt_dec n0 n) as [H'|H']; auto.
 generalize (H _ H'); dec.
 intuition; simpl.
 destruct (orb_false_elim _ _ (H _ H0)); auto.
 replace m with (S (pred m)) by omega.
 assert (n <= pred m) by omega.
 destruct (orb_false_elim _ _ (H _ H1)); auto.
 intuition; simpl.
 replace m with (S (pred m)) by omega.
 apply H; omega.
 intuition; simpl.
 replace m with (S (S (m-2))) by omega.
 apply H; omega.
 intuition; simpl; destruct (orb_false_elim _ _ (H _ H0)); auto.
 rename n into k; rename n0 into n.
 intuition; simpl.
 generalize (H _ H1).
 rewrite existsb_forall; auto.
 rewrite existsb_forall; auto.
 intuition; simpl.
 destruct (orb_false_elim _ _ (H _ H0)); auto.
 destruct p as (k,t').
 intros.
 assert (n <= m-k) by omega.
 destruct (orb_false_elim _ _ (H _ H2)); auto.
 rewrite existsb_forall in H4.
 generalize (H4 _ H0).
 replace (k+(m-k)) with m by omega; auto.
 rewrite H0; simpl; auto.
 rewrite existsb_forall; intros.
 destruct x as (k,t').
 apply (H1 _ H2); omega.
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
   clos_after n t <-> (forall m u, n <= m -> t[m:=u] = t).
Proof.
 apply (term_ind2_one 
         (fun t n => clos_after n t <-> (forall m u, n<=m -> t[m:=u] = t))); 
  simpl; intros; simpl_clos_after; auto.
 (* Dummy *)
 intuition.
 (* Var *)
 intuition; try dec.
 destruct (le_lt_dec n k) as [H'|H']; auto.
 generalize (H k TDummy H'); dec.
 (* Let *)
 rename H into IHt1; rename H0 into IHt2.
 rewrite IHt1; rewrite IHt2; clear IHt1 IHt2; simpl in *; intuition.
 assert (H1:=H _ u H0).
 injection H1; auto.
 replace m with (S (pred m)) by omega.
 assert (n <= pred m) by omega.
 assert (H2:=H _ u H1).
 injection H2; auto.
 (* Fun *)
 rename H into IHt.
 rewrite IHt; intuition.
 replace m with (S (pred m)) by omega.
 assert (n <= pred m) by omega.
 generalize (H _ u H1); inversion 1; auto.
 (* Fix *)
 rename H into IHt.
 rewrite IHt; intuition.
 replace m with (S (S (m-2))) by omega.
 assert (n <= m-2) by omega.
 generalize (H _ u H1); inversion 1; auto.
 (* Apply *)
 rename H into IHt1; rename H0 into IHt2.
 rewrite IHt1; rewrite IHt2.
 intuition.
 generalize (H _ u H0); inversion 1; auto.
 generalize (H _ u H0); inversion 1; auto.
 (* Constr *)
 rename H into Htl.
 split; intros.
 f_equal.
 rewrite map_id; intros.
 generalize (H _ H1); rewrite Htl; auto.
 rename u into r.
 rewrite (Htl n _ H0); clear Htl; intros.
 revert r H0.
 rewrite <- map_id.
 generalize (H _ u H1); injection 1; auto.
 (* Match *)
 rename H into IHt; rename H0 into IHpl.
 rewrite IHt; clear IHt.
 intuition.
 f_equal; auto.
 rewrite map_id; intros.
 destruct a; f_equal.
 generalize (H1 _ H2); destruct (IHpl n _ H2) as (A,_); auto with arith.
 generalize (H _ u H0); injection 1; auto.
 destruct p.
 destruct (IHpl n _ H0) as (_,A); apply A; clear A; intros; simpl in *.
 replace m with (n0+(m-n0)) by omega.
 assert (H2: n <= m-n0) by omega.
 generalize (H _ u H2).
 intros H3; injection H3; clear H3; rewrite map_id; intros.
 generalize (H3 _ H0).
 injection 1; auto with arith.
 (* Stuff about lists. *)
 intuition.
 destruct H1; try subst; auto.
 intuition.
 destruct H1; try subst; auto.
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
intros t n u m H Hu; revert n m H.
apply (term_ind2_one 
         (fun t n => forall m, n <= m -> clos_after (S m) t -> clos_after m (t[n:=u]))); 
 simpl; intros; simpl_clos_after; intuition auto with arith.
dec.
simpl_clos_after; omega.
red in H0; red; auto.
simpl_clos_after; omega.
rewrite in_map_iff in H2; destruct H2 as (r,(A,B)); subst u0; auto.
rewrite in_map_iff in H2; destruct H2 as (p',(A,B)); subst p; simpl; auto.
 destruct p'.
apply (H0 n _ B); auto with arith.
generalize (H4 _ B); rewrite plus_n_Sm; auto with arith.
subst; auto.
subst; auto.
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
revert n.
pattern t; apply term_ind2_zero; simpl; intuition; try subst; auto.
dec; destruct (k-n); auto with arith.
f_equal; symmetry; rewrite map_id; symmetry; auto.
f_equal; auto; symmetry; rewrite map_id; symmetry; auto.
 generalize (H0 _ H1); destruct a; auto.
(* cons *)
inv_clear H.
rewrite IHl; auto.
revert n.
pattern t; apply term_ind2_zero; intros; simpl; auto.
(* - var *)
repeat dec.
 subst k; replace (n-n) with 0 by omega; simpl.
 rewrite <- IHl; auto.
 replace (k-n) with (S (pred k - n)) by omega; simpl.
 f_equal; f_equal; omega.
(* - constr *)
f_equal; rewrite map_map; rewrite map_ext_iff; auto.
(* - match *)
f_equal; auto.
rewrite map_map; rewrite map_ext_iff.
intros; destruct a0; f_equal; auto.
(* - misc *)
generalize (H0 _ H1); simpl; auto.
simpl in *; intuition.
simpl in *; intuition; subst; auto.
simpl in *; intuition.
simpl in *; intuition; subst; auto.
Qed.

Lemma subst_commut : forall u u', clos u -> clos u' -> 
 forall t n n', n<=n' -> t[S n':=u'][n:=u] = t[n:=u][n':=u'].
Proof.
intros u u' Hu Hu' t; pattern t; apply term_ind2_zero; simpl; intuition auto with arith.
repeat dec; auto.
f_equal.
do 2 rewrite map_map; rewrite map_ext_iff; intros; auto.
f_equal; auto.
do 2 rewrite map_map; rewrite map_ext_iff; intros; destruct a; f_equal; auto.
repeat rewrite <- plus_n_Sm; generalize (H0 _ H2); simpl; auto with arith.
subst; auto.
subst; auto.
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




(******* A SUIVRE ! *******)




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
