(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export SetoidList.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Ordered types *)

Inductive Compare (X : Set) (lt eq : X -> X -> Prop) (x y : X) : Set :=
  | LT : lt x y -> Compare lt eq x y
  | EQ : eq x y -> Compare lt eq x y
  | GT : lt y x -> Compare lt eq x y.

Module Type OrderedType.

  Parameter Inline t : Set.

  Parameter Inline eq : t -> t -> Prop.
  Parameter Inline lt : t -> t -> Prop.

  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

End OrderedType.

(** * Ordered types properties *)

(** Additional properties that can be derived from signature
    [OrderedType]. *)

Module OrderedTypeFacts (O: OrderedType). 
  Import O.

  Lemma lt_antirefl : forall x, ~ lt x x.
  Proof.
   intros; intro; absurd (eq x x); auto. 
  Qed.

  Lemma lt_eq : forall x y z, lt x y -> eq y z -> lt x z.
  Proof. 
   intros; destruct (compare x z); auto.
   elim (lt_not_eq H); apply eq_trans with z; auto.
   elim (lt_not_eq (lt_trans l H)); auto.
  Qed. 

  Lemma eq_lt : forall x y z, eq x y -> lt y z -> lt x z.    
  Proof.
   intros; destruct (compare x z); auto.
   elim (lt_not_eq H0); apply eq_trans with x; auto.
   elim (lt_not_eq (lt_trans H0 l)); auto.
  Qed. 

  Lemma le_eq : forall x y z, ~lt x y -> eq y z -> ~lt x z.
  Proof.
   intros; intro; destruct H; apply lt_eq with z; auto.
  Qed.

  Lemma eq_le : forall x y z, eq x y -> ~lt y z -> ~lt x z.
  Proof.
   intros; intro; destruct H0; apply eq_lt with x; auto.
  Qed.

  Lemma neq_eq : forall x y z, ~eq x y -> eq y z -> ~eq x z.
  Proof.
   intros; intro; destruct H; apply eq_trans with z; auto.
  Qed.

  Lemma eq_neq : forall x y z, eq x y -> ~eq y z -> ~eq x z.
  Proof.
   intros; intro; destruct H0; apply eq_trans with x; auto.
  Qed.

  Hint Immediate eq_lt lt_eq le_eq eq_le neq_eq eq_neq.

  Lemma le_lt_trans : forall x y z, ~lt y x -> lt y z -> lt x z.
  Proof.
   intros; destruct (compare y x); auto.
   elim (H l).
   apply eq_lt with y; auto.
   apply lt_trans with y; auto.
  Qed.

  Lemma lt_le_trans : forall x y z, lt x y -> ~lt z y -> lt x z.
  Proof.
   intros; destruct (compare z y); auto.
   elim (H0 l).
   apply lt_eq with y; auto.
   apply lt_trans with y; auto.
  Qed.

  Lemma le_neq : forall x y, ~lt x y -> ~eq x y -> lt y x.
  Proof. 
   intros; destruct (compare x y); intuition.
  Qed.

  Lemma neq_sym : forall x y, ~eq x y -> ~eq y x.
  Proof. 
   intuition.
  Qed.

(* TODO concernant la tactique order: 
   * propagate_lt n'est sans doute pas complet
   * un propagate_le
   * exploiter les hypotheses negatives restant a la fin
   * faire que ca marche meme quand une hypothese depend d'un eq ou lt.
*) 

Ltac abstraction := match goal with 
 (* First, some obvious simplifications *)
 | H : False |- _ => elim H
 | H : lt ?x ?x |- _ => elim (lt_antirefl H)
 | H : ~eq ?x ?x |- _ => elim (H (eq_refl x))
 | H : eq ?x ?x |- _ => clear H; abstraction
 | H : ~lt ?x ?x |- _ => clear H; abstraction
 | |- eq ?x ?x => exact (eq_refl x)
 | |- lt ?x ?x => elimtype False; abstraction
 | |- ~ _ => intro; abstraction
 | H1: ~lt ?x ?y, H2: ~eq ?x ?y |- _ => 
     generalize (le_neq H1 H2); clear H1 H2; intro; abstraction
 | H1: ~lt ?x ?y, H2: ~eq ?y ?x |- _ => 
     generalize (le_neq H1 (neq_sym H2)); clear H1 H2; intro; abstraction
 (* Then, we generalize all interesting facts *)
 | H : ~eq ?x ?y |- _ =>  revert H; abstraction
 | H : ~lt ?x ?y |- _ => revert H; abstraction  
 | H : lt ?x ?y |- _ => revert H; abstraction
 | H : eq ?x ?y |- _ =>  revert H; abstraction
 | _ => idtac
end.

Ltac do_eq a b EQ := match goal with 
 | |- lt ?x ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_lt (eq_sym EQ) H); clear H; intro H) ||
      (generalize (lt_eq H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ
 | |- ~lt ?x ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_le (eq_sym EQ) H); clear H; intro H) ||
      (generalize (le_eq H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ 
 | |- eq ?x ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_trans (eq_sym EQ) H); clear H; intro H) ||
      (generalize (eq_trans H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ 
 | |- ~eq ?x ?y -> _ => let H := fresh "H" in 
     (intro H; 
      (generalize (eq_neq (eq_sym EQ) H); clear H; intro H) ||
      (generalize (neq_eq H EQ); clear H; intro H) || 
      idtac); 
      do_eq a b EQ 
 | |- lt a ?y => apply eq_lt with b; [exact EQ|]
 | |- lt ?y a => apply lt_eq with b; [|exact (eq_sym EQ)]
 | |- eq a ?y => apply eq_trans with b; [exact EQ|]
 | |- eq ?y a => apply eq_trans with b; [|exact (eq_sym EQ)]
 | _ => idtac
 end.

Ltac propagate_eq := abstraction; clear; match goal with 
 (* the abstraction tactic leaves equality facts in head position...*)
 | |- eq ?a ?b -> _ => 
     let EQ := fresh "EQ" in (intro EQ; do_eq a b EQ; clear EQ); 
     propagate_eq 
 | _ => idtac
end.

Ltac do_lt x y LT := match goal with 
 (* LT *)
 | |- lt x y -> _ => intros _; do_lt x y LT
 | |- lt y ?z -> _ => let H := fresh "H" in 
     (intro H; generalize (lt_trans LT H); intro); do_lt x y LT
 | |- lt ?z x -> _ => let H := fresh "H" in 
     (intro H; generalize (lt_trans H LT); intro); do_lt x y LT
 | |- lt _ _ -> _ => intro; do_lt x y LT
 (* GE *)
 | |- ~lt y x -> _ => intros _; do_lt x y LT
 | |- ~lt x ?z -> _ => let H := fresh "H" in 
     (intro H; generalize (le_lt_trans H LT); intro); do_lt x y LT
 | |- ~lt ?z y -> _ => let H := fresh "H" in 
     (intro H; generalize (lt_le_trans LT H); intro); do_lt x y LT
 | |- ~lt _ _ -> _ => intro; do_lt x y LT
 | _ => idtac
 end.

Definition hide_lt := lt.

Ltac propagate_lt := abstraction; match goal with 
 (* when no [=] remains, the abstraction tactic leaves [<] facts first. *)
 | |- lt ?x ?y -> _ => 
     let LT := fresh "LT" in (intro LT; do_lt x y LT; 
     change (hide_lt x y) in LT); 
     propagate_lt 
 | _ => unfold hide_lt in *
end.

Ltac order := 
 intros; 
 propagate_eq; 
 propagate_lt; 
 auto; 
 propagate_lt; 
 eauto.

Ltac false_order := elimtype False; order.

  Lemma gt_not_eq : forall x y, lt y x -> ~ eq x y.
  Proof.
    order.
  Qed.	
 
  Lemma eq_not_lt : forall x y : t, eq x y -> ~ lt x y.
  Proof. 
    order.
  Qed.

  Hint Resolve gt_not_eq eq_not_lt.

  Lemma eq_not_gt : forall x y : t, eq x y -> ~ lt y x.
  Proof. 
   order.
  Qed.

  Lemma lt_not_gt : forall x y : t, lt x y -> ~ lt y x.
  Proof.  
   order.
  Qed.

  Hint Resolve eq_not_gt lt_antirefl lt_not_gt.

  Lemma elim_compare_eq :
   forall x y : t,
   eq x y -> exists H : eq x y, compare x y = EQ _ H.
  Proof. 
   intros; case (compare x y); intros H'; try solve [false_order].
   exists H'; auto.   
  Qed.

  Lemma elim_compare_lt :
   forall x y : t,
   lt x y -> exists H : lt x y, compare x y = LT _ H.
  Proof. 
   intros; case (compare x y); intros H'; try solve [false_order].
   exists H'; auto. 
  Qed.

  Lemma elim_compare_gt :
   forall x y : t,
   lt y x -> exists H : lt y x, compare x y = GT _ H.
  Proof. 
   intros; case (compare x y); intros H'; try solve [false_order].
   exists H'; auto.   
  Qed.

  Ltac elim_comp := 
    match goal with 
      | |- ?e => match e with 
           | context ctx [ compare ?a ?b ] =>
                let H := fresh in 
                (destruct (compare a b) as [H|H|H]; 
                 try solve [ intros; false_order])
         end
    end.

  Ltac elim_comp_eq x y :=
    elim (elim_compare_eq (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ]. 

  Ltac elim_comp_lt x y :=
    elim (elim_compare_lt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ]. 

  Ltac elim_comp_gt x y :=
    elim (elim_compare_gt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
   intros; elim (compare x y); [ right | left | right ]; auto.
  Defined.
 
  Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
  Proof.
   intros; elim (compare x y); [ left | right | right ]; auto.
  Defined.

  Definition eqb x y : bool := if eq_dec x y then true else false.

  Lemma eqb_alt : 
    forall x y, eqb x y = match compare x y with EQ _ => true | _ => false end. 
  Proof.
  unfold eqb; intros; destruct (eq_dec x y); elim_comp; auto.
  Qed.

(* Specialization of resuts about lists modulo. *)

Section ForNotations.

Notation In:=(InA eq).
Notation Inf:=(lelistA lt).
Notation Sort:=(sort lt).
Notation NoDup:=(NoDupA eq).

Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
Proof. exact (InA_eqA eq_sym eq_trans). Qed.

Lemma ListIn_In : forall l x, List.In x l -> In x l.
Proof. exact (In_InA eq_refl). Qed.

Lemma Inf_lt : forall l x y, lt x y -> Inf y l -> Inf x l.
Proof. exact (InfA_ltA lt_trans). Qed.
 
Lemma Inf_eq : forall l x y, eq x y -> Inf y l -> Inf x l.
Proof. exact (InfA_eqA eq_lt). Qed.

Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> lt a x.
Proof. exact (SortA_InfA_InA eq_refl eq_sym lt_trans lt_eq eq_lt). Qed.
  
Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> lt x y) -> Inf x l.
Proof. exact (@In_InfA t lt). Qed.

Lemma In_Inf : forall l x, (forall y, In y l -> lt x y) -> Inf x l.
Proof. exact (InA_InfA eq_refl (ltA:=lt)). Qed.

Lemma Inf_alt : 
 forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> lt x y)).
Proof. exact (InfA_alt eq_refl eq_sym lt_trans lt_eq eq_lt). Qed.

Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
Proof. exact (SortA_NoDupA eq_refl eq_sym lt_trans lt_not_eq lt_eq eq_lt) . Qed.

End ForNotations.

Hint Resolve ListIn_In Sort_NoDup Inf_lt. 
Hint Immediate In_eq Inf_lt. 

End OrderedTypeFacts.

Module KeyOrderedType(O:OrderedType).
 Import O.
 Module MO:=OrderedTypeFacts(O).
 Import MO.

 Section Elt.
 Variable elt : Set.
 Notation key:=t.

  Definition eqk (p p':key*elt) := eq (fst p) (fst p').
  Definition eqke (p p':key*elt) := 
          eq (fst p) (fst p') /\ (snd p) = (snd p').
  Definition ltk (p p':key*elt) := lt (fst p) (fst p').

  Hint Unfold eqk eqke ltk.
  Hint Extern 2 (eqke ?a ?b) => split.

   (* eqke is stricter than eqk *)
 
   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
   Proof.
     unfold eqk, eqke; intuition.
   Qed.

  (* ltk ignore the second components *)

   Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
   Proof. auto. Qed.

   Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
   Proof. auto. Qed.
   Hint Immediate ltk_right_r ltk_right_l.

  (* eqk, eqke are equalities, ltk is a strict order *)
 
  Lemma eqk_refl : forall e, eqk e e.
  Proof. auto. Qed.

  Lemma eqke_refl : forall e, eqke e e.
  Proof. auto. Qed.

  Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
  Proof. auto. Qed.

  Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
  Proof. unfold eqke; intuition. Qed.

  Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
  Proof. eauto. Qed.

  Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
  Proof.
    unfold eqke; intuition; [ eauto | congruence ].
  Qed.

  Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
  Proof. eauto. Qed.

  Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
  Proof. unfold eqk, ltk; auto. Qed.  

  Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
  Proof.
    unfold eqke, ltk; intuition; simpl in *; subst.
    exact (lt_not_eq H H1).
  Qed.

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
  Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke.
  Hint Immediate eqk_sym eqke_sym.

  (* Additionnal facts *)

  Lemma eqk_not_ltk : forall x x', eqk x x' -> ~ltk x x'.
   Proof.
     unfold eqk, ltk; simpl; auto.
   Qed.

  Lemma ltk_eqk : forall e e' e'', ltk e e' -> eqk e' e'' -> ltk e e''.
  Proof. eauto. Qed.

  Lemma eqk_ltk : forall e e' e'', eqk e e' -> ltk e' e'' -> ltk e e''.
  Proof.
      intros (k,e) (k',e') (k'',e'').
      unfold ltk, eqk; simpl; eauto.
  Qed.
  Hint Resolve eqk_not_ltk. 
  Hint Immediate ltk_eqk eqk_ltk.

  Lemma InA_eqke_eqk : 
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition.
  Qed.
  Hint Resolve InA_eqke_eqk.

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.
  Notation Sort := (sort ltk).
  Notation Inf := (lelistA ltk).

  Hint Unfold MapsTo In.

  (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

  Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
  Proof.
  firstorder.
  exists x; auto.
  induction H.
  destruct y.
  exists e; auto.
  destruct IHInA as [e H0].
  exists e; auto.
  Qed.

  Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
  Proof.
  intros; unfold MapsTo in *; apply InA_eqA with (x,e); eauto.
  Qed.

  Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
  Proof.
  destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
  Qed. 

  Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
  Proof. exact (InfA_eqA eqk_ltk). Qed.

  Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
  Proof. exact (InfA_ltA ltk_trans). Qed.

  Hint Immediate Inf_eq.
  Hint Resolve Inf_lt.

  Lemma Sort_Inf_In : 
      forall l p q, Sort l -> Inf q l -> InA eqk p l -> ltk q p.
  Proof. 
  exact (SortA_InfA_InA eqk_refl eqk_sym ltk_trans ltk_eqk eqk_ltk).
  Qed.

  Lemma Sort_Inf_NotIn : 
      forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
  Proof.
    intros; red; intros.
    destruct H1 as [e' H2].
    elim (@ltk_not_eqk (k,e) (k,e')).
    eapply Sort_Inf_In; eauto.
    red; simpl; auto.
  Qed.

  Lemma Sort_NoDupA: forall l, Sort l -> NoDupA eqk l.
  Proof. 
  exact (SortA_NoDupA eqk_refl eqk_sym ltk_trans ltk_not_eqk ltk_eqk eqk_ltk).
  Qed.

  Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
  Proof.
   inversion 1; intros; eapply Sort_Inf_In; eauto.
  Qed.

  Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
      ltk e e' \/ eqk e e'.
  Proof.
    inversion_clear 2; auto.
    left; apply Sort_In_cons_1 with l; auto.
  Qed.

  Lemma Sort_In_cons_3 : 
    forall x l k e, Sort ((k,e)::l) -> In x l -> ~eq x k.
  Proof.
    inversion_clear 1; red; intros.
    destruct (Sort_Inf_NotIn H0 H1 (In_eq H2 H)).
  Qed.

  Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
  Proof.
    inversion 1.
    inversion_clear H0; eauto.
    destruct H1; simpl in *; intuition.
  Qed.      

  Lemma In_inv_2 : forall k k' e e' l, 
      InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
  Proof.  
   inversion_clear 1; compute in H0; intuition.
  Qed.

  Lemma In_inv_3 : forall x x' l, 
      InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
  Proof.
   inversion_clear 1; compute in H0; intuition.
  Qed.

 End Elt.

 Hint Unfold eqk eqke ltk.
 Hint Extern 2 (eqke ?a ?b) => split.
 Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
 Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke.
 Hint Immediate eqk_sym eqke_sym.
 Hint Resolve eqk_not_ltk. 
 Hint Immediate ltk_eqk eqk_ltk.
 Hint Resolve InA_eqke_eqk.
 Hint Unfold MapsTo In.
 Hint Immediate Inf_eq.
 Hint Resolve Inf_lt.
 Hint Resolve Sort_Inf_NotIn.
 Hint Resolve In_inv_2 In_inv_3.

End KeyOrderedType.


