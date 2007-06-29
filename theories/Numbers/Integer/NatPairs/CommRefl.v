Require Import Arith.
Require Import List.
Require Import Setoid.

Inductive bin : Set := node : bin->bin->bin | leaf : nat->bin.

Fixpoint flatten_aux (t fin:bin){struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Fixpoint nat_le_bool (n m:nat){struct m} : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n, S m => nat_le_bool n m
  end.

Fixpoint insert_bin (n:nat)(t:bin){struct t} : bin :=
  match t with
  | leaf m => match nat_le_bool n m with
              | true => node (leaf n)(leaf m)
              | false => node (leaf m)(leaf n)
              end
  | node (leaf m) t' => match nat_le_bool n m with
                        | true => node (leaf n) t
                        | false => 
                            node (leaf m)(insert_bin n t')
                        end
  | t => node (leaf n) t
  end.

Fixpoint sort_bin (t:bin) : bin :=
  match t with
  | node (leaf n) t' => insert_bin n (sort_bin t')
  | t => t
  end.

Section commut_eq.
Variable A : Set.
Variable E : relation A.
Variable f : A -> A -> A.

Hypothesis E_equiv : equiv A E.
Hypothesis comm : forall x y : A, f x y = f y x.
Hypothesis assoc : forall x y z : A, f x (f y z) = f (f x y) z.

Notation "x == y" := (E x y) (at level 70).

Add Relation A E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Fixpoint bin_A (l:list A)(def:A)(t:bin){struct t} : A :=
  match t with
  | node t1 t2 => f (bin_A l def t1)(bin_A l def t2)
  | leaf n => nth n l def
  end.
 Theorem flatten_aux_valid_A :
 forall (l:list A)(def:A)(t t':bin),
  f (bin_A l def t)(bin_A l def t') == bin_A l def (flatten_aux t t').
Proof.
 intros l def t; elim t; simpl; auto.
 intros t1 IHt1 t2 IHt2 t'.  rewrite <- IHt1; rewrite <- IHt2.
 symmetry; apply assoc.
Qed.
 Theorem flatten_valid_A :
 forall (l:list A)(def:A)(t:bin),
   bin_A l def t == bin_A l def (flatten t).
Proof.
 intros l def t; elim t; simpl; trivial.
 intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A; rewrite <- IHt2.
 trivial.
Qed.

Theorem flatten_valid_A_2 :
 forall (t t':bin)(l:list A)(def:A),
   bin_A l def (flatten t) == bin_A l def (flatten t')->
   bin_A l def t == bin_A l def t'. 
Proof.
 intros t t' l def Heq.
 rewrite (flatten_valid_A l def t); rewrite (flatten_valid_A l def t').
 trivial.
Qed.

Theorem insert_is_f : forall (l:list A)(def:A)(n:nat)(t:bin),
   bin_A l def (insert_bin n t) == 
   f (nth n l def) (bin_A l def t).
Proof.
 intros l def n t; elim t.
 intros t1; case t1.
 intros t1' t1'' IHt1 t2 IHt2.
 simpl.
 auto.
 intros n0 IHt1 t2 IHt2.
 simpl.
 case (nat_le_bool n n0).
 simpl.
 auto.
 simpl.
 rewrite IHt2.
 repeat rewrite assoc; rewrite (comm (nth n l def)); auto.
 simpl.
 intros n0; case (nat_le_bool n n0); auto.
 rewrite comm; auto.
Qed.

Theorem sort_eq : forall (l:list A)(def:A)(t:bin),
    bin_A l def (sort_bin t) == bin_A l def t.  
Proof.
 intros l def t; elim t.
 intros t1 IHt1; case t1.
 auto.
 intros n t2 IHt2; simpl; rewrite insert_is_f.
 rewrite IHt2; auto.
 auto.
Qed.


Theorem sort_eq_2 :
 forall (l:list A)(def:A)(t1 t2:bin),
   bin_A l def (sort_bin t1) == bin_A l def (sort_bin t2)->
   bin_A l def t1 == bin_A l def t2.  
Proof.
 intros l def t1 t2.
 rewrite <- (sort_eq l def t1); rewrite <- (sort_eq l def t2).
 trivial.
Qed.

End commut_eq.


Ltac term_list f l v :=
  match v with
  | (f ?X1 ?X2) =>
    let l1 := term_list f l X2 in term_list f l1 X1
  | ?X1 => constr:(cons X1 l)
  end.

Ltac compute_rank l n v :=
  match l with
  | (cons ?X1 ?X2) =>
    let tl := constr:X2 in
    match constr:(X1 == v) with
    | (?X1 == ?X1) => n
    | _ => compute_rank tl (S n) v
    end
  end.

Ltac model_aux l f v :=
  match v with
  | (f ?X1 ?X2) =>
    let r1 := model_aux l f X1 with r2 := model_aux l f X2 in
      constr:(node r1 r2)
  | ?X1 => let n := compute_rank l 0 X1 in constr:(leaf n)
  | _ => constr:(leaf 0)
  end.

Ltac comm_eq A f assoc_thm comm_thm :=
  match goal with
  | [ |- (?X1 == ?X2 :>A) ] =>
    let l := term_list f (nil (A:=A)) X1 in
    let term1 := model_aux l f X1 
    with term2 := model_aux l f X2 in
    (change (bin_A A f l X1 term1 == bin_A A f l X1 term2);
      apply flatten_valid_A_2 with (1 := assoc_thm);
      apply sort_eq_2 with (1 := comm_thm)(2 := assoc_thm); 
      auto)
  end.

(*
Theorem reflection_test4 : forall x y z:nat, x+(y+z) = (z+x)+y.
Proof.
 intros x y z. comm_eq nat plus plus_assoc plus_comm.
Qed.
*)