
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    Permutation.v                        
                                                                     
    Defintion and properties of permutations                         
   **********************************************************************)
Require Export List.
Require Export ListAux.
 
Section permutation.
Variable A : Set.

(************************************** 
   Definition of permutations as sequences of adjacent transpositions
 **************************************)
 
Inductive permutation : list A -> list A -> Prop :=
  | permutation_nil : permutation nil nil
  | permutation_skip :
      forall (a : A) (l1 l2 : list A),
      permutation l2 l1 -> permutation (a :: l2) (a :: l1)
  | permutation_swap :
      forall (a b : A) (l : list A), permutation (a :: b :: l) (b :: a :: l)
  | permutation_trans :
      forall l1 l2 l3 : list A,
      permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
Hint Constructors permutation.

(************************************** 
   Reflexivity
 **************************************)
 
Theorem permutation_refl : forall l : list A, permutation l l.
simple induction l.
apply permutation_nil.
intros a l1 H.
apply permutation_skip with (1 := H).
Qed.
Hint Resolve permutation_refl.

(************************************** 
   Symmetry
   **************************************)
 
Theorem permutation_sym :
 forall l m : list A, permutation l m -> permutation m l.
intros l1 l2 H'; elim H'.
apply permutation_nil.
intros a l1' l2' H1 H2.
apply permutation_skip with (1 := H2).
intros a b l1'.
apply permutation_swap.
intros l1' l2' l3' H1 H2 H3 H4.
apply permutation_trans with (1 := H4) (2 := H2).
Qed.

(************************************** 
   Compatibility with list length
   **************************************)
 
Theorem permutation_length :
 forall l m : list A, permutation l m -> length l = length m.
intros l m H'; elim H'; simpl in |- *; auto.
intros l1 l2 l3 H'0 H'1 H'2 H'3.
rewrite <- H'3; auto.
Qed.

(************************************** 
   A permutation of the nil list is the nil list
   **************************************)
 
Theorem permutation_nil_inv : forall l : list A, permutation l nil -> l = nil.
intros l H; generalize (permutation_length _ _ H); case l; simpl in |- *;
 auto.
intros; discriminate.
Qed.
 
(************************************** 
   A permutation of the singleton list is the singleton list
   **************************************)
 
Let permutation_one_inv_aux :
  forall l1 l2 : list A,
  permutation l1 l2 -> forall a : A, l1 = a :: nil -> l2 = a :: nil.
intros l1 l2 H; elim H; clear H l1 l2; auto.
intros a l3 l4 H0 H1 b H2.
eq_tac.
injection H2; auto.
apply permutation_nil_inv; auto.
injection H2; intros H3 H4; rewrite <- H3; auto.
apply permutation_sym; auto.
intros; discriminate.
Qed.

Theorem permutation_one_inv :
 forall (a : A) (l : list A), permutation (a :: nil) l -> l = a :: nil.
intros a l H; apply permutation_one_inv_aux with (l1 := a :: nil); auto.
Qed.

(************************************** 
   Compatibility with the belonging
   **************************************)
 
Theorem permutation_in :
 forall (a : A) (l m : list A), permutation l m -> In a l -> In a m.
intros a l m H; elim H; simpl in |- *; auto; intuition.
Qed.

(************************************** 
   Compatibility with the append function
   **************************************)
 
Theorem permutation_app_comp :
 forall l1 l2 l3 l4,
 permutation l1 l2 -> permutation l3 l4 -> permutation (l1 ++ l3) (l2 ++ l4).
intros l1 l2 l3 l4 H1; generalize l3 l4; elim H1; clear H1 l1 l2 l3 l4;
 simpl in |- *; auto.
intros a b l l3 l4 H.
cut (permutation (l ++ l3) (l ++ l4)); auto.
intros; apply permutation_trans with (a :: b :: l ++ l4); auto.
elim l; simpl in |- *; auto.
intros l1 l2 l3 H H0 H1 H2 l4 l5 H3.
apply permutation_trans with (l2 ++ l4); auto.
Qed.
Hint Resolve permutation_app_comp.

(************************************** 
   Swap two sublists
   **************************************)
 
Theorem permutation_app_swap :
 forall l1 l2, permutation (l1 ++ l2) (l2 ++ l1).
intros l1; elim l1; auto.
intros; rewrite <- app_nil_end; auto.
intros a l H l2.
replace (l2 ++ a :: l) with ((l2 ++ a :: nil) ++ l).
apply permutation_trans with (l ++ l2 ++ a :: nil); auto.
apply permutation_trans with (((a :: nil) ++ l2) ++ l); auto.
simpl in |- *; auto.
apply permutation_trans with (l ++ (a :: nil) ++ l2); auto.
apply permutation_sym; auto.
replace (l2 ++ a :: l) with ((l2 ++ a :: nil) ++ l).
apply permutation_app_comp; auto.
elim l2; simpl in |- *; auto.
intros a0 l0 H0.
apply permutation_trans with (a0 :: a :: l0); auto.
apply (app_ass l2 (a :: nil) l).
apply (app_ass l2 (a :: nil) l).
Qed.

(************************************** 
   A transposition is a permutation
   **************************************)
 
Theorem permutation_transposition :
 forall a b l1 l2 l3,
 permutation (l1 ++ a :: l2 ++ b :: l3) (l1 ++ b :: l2 ++ a :: l3).
intros a b l1 l2 l3.
apply permutation_app_comp; auto.
change
  (permutation ((a :: nil) ++ l2 ++ (b :: nil) ++ l3)
     ((b :: nil) ++ l2 ++ (a :: nil) ++ l3)) in |- *.
repeat rewrite <- app_ass.
apply permutation_app_comp; auto.
apply permutation_trans with ((b :: nil) ++ (a :: nil) ++ l2); auto.
apply permutation_app_swap; auto.
repeat rewrite app_ass.
apply permutation_app_comp; auto.
apply permutation_app_swap; auto.
Qed.

(************************************** 
   An element of a list can be put on top of the list to get a permutation
   **************************************)
 
Theorem in_permutation_ex :
 forall a l, In a l -> exists l1 : list A, permutation (a :: l1) l.
intros a l; elim l; simpl in |- *; auto.
intros H; case H; auto.
intros a0 l0 H [H0| H0].
exists l0; rewrite H0; auto.
case H; auto; intros l1 Hl1; exists (a0 :: l1).
apply permutation_trans with (a0 :: a :: l1); auto.
Qed.
 
(************************************** 
   A permutation of a cons can be inverted
   **************************************)

Let permutation_cons_ex_aux :
  forall (a : A) (l1 l2 : list A),
  permutation l1 l2 ->
  forall l11 l12 : list A,
  l1 = l11 ++ a :: l12 ->
  exists l3 : list A,
    (exists l4 : list A,
       l2 = l3 ++ a :: l4 /\ permutation (l11 ++ l12) (l3 ++ l4)).
intros a l1 l2 H; elim H; clear H l1 l2.
intros l11 l12; case l11; simpl in |- *; intros; discriminate.
intros a0 l1 l2 H H0 l11 l12; case l11; simpl in |- *.
exists (nil (A:=A)); exists l1; simpl in |- *; split; auto.
eq_tac; injection H1; auto.
injection H1; intros H2 H3; rewrite <- H2; auto.
intros a1 l111 H1.
case (H0 l111 l12); auto.
injection H1; auto.
intros l3 (l4, (Hl1, Hl2)).
exists (a0 :: l3); exists l4; split; simpl in |- *; auto.
eq_tac; injection H1; auto.
injection H1; intros H2 H3; rewrite H3; auto.
intros a0 b l l11 l12; case l11; simpl in |- *.
case l12; try (intros; discriminate).
intros a1 l0 H; exists (b :: nil); exists l0; simpl in |- *; split; auto.
repeat eq_tac; injection H; auto.
injection H; intros H1 H2 H3; rewrite H2; auto.
intros a1 l111; case l111; simpl in |- *.
intros H; exists (nil (A:=A)); exists (a0 :: l12); simpl in |- *; split; auto.
repeat eq_tac; injection H; auto.
injection H; intros H1 H2 H3; rewrite H3; auto.
intros a2 H1111 H; exists (a2 :: a1 :: H1111); exists l12; simpl in |- *;
 split; auto.
repeat eq_tac; injection H; auto.
intros l1 l2 l3 H H0 H1 H2 l11 l12 H3.
case H0 with (1 := H3).
intros l4 (l5, (Hl1, Hl2)).
case H2 with (1 := Hl1).
intros l6 (l7, (Hl3, Hl4)).
exists l6; exists l7; split; auto.
apply permutation_trans with (1 := Hl2); auto.
Qed.
 
Theorem permutation_cons_ex :
 forall (a : A) (l1 l2 : list A),
 permutation (a :: l1) l2 ->
 exists l3 : list A,
   (exists l4 : list A, l2 = l3 ++ a :: l4 /\ permutation l1 (l3 ++ l4)).
intros a l1 l2 H.
apply (permutation_cons_ex_aux a (a :: l1) l2 H nil l1); simpl in |- *; auto.
Qed.

(************************************** 
   A permutation can be simply inverted if the two list starts with a cons
   **************************************)
 
Theorem permutation_inv :
 forall (a : A) (l1 l2 : list A),
 permutation (a :: l1) (a :: l2) -> permutation l1 l2.
intros a l1 l2 H; case permutation_cons_ex with (1 := H).
intros l3 (l4, (Hl1, Hl2)).
apply permutation_trans with (1 := Hl2).
generalize Hl1; case l3; simpl in |- *; auto.
intros H1; injection H1; intros H2; rewrite H2; auto.
intros a0 l5 H1; injection H1; intros H2 H3; rewrite H2; rewrite H3; auto.
apply permutation_trans with (a0 :: l4 ++ l5); auto.
apply permutation_skip; apply permutation_app_swap.
apply (permutation_app_swap (a0 :: l4) l5).
Qed.

(************************************** 
   Take a list and return tle list of all pairs of an element of the 
   list and the remaining list
   **************************************)
 
Fixpoint split_one (l : list A) : list (A * list A) :=
  match l with
  | nil => nil (A:=A * list A)
  | a :: l1 =>
      (a, l1)
      :: map (fun p : A * list A => (fst p, a :: snd p)) (split_one l1)
  end.

(************************************** 
   The pairs of the list are a permutation
   **************************************)
 
Theorem split_one_permutation :
 forall (a : A) (l1 l2 : list A),
 In (a, l1) (split_one l2) -> permutation (a :: l1) l2.
intros a l1 l2; generalize a l1; elim l2; clear a l1 l2; simpl in |- *; auto.
intros a l1 H1; case H1.
intros a l H a0 l1 [H0| H0].
injection H0; intros H1 H2; rewrite H2; rewrite H1; auto.
generalize H H0; elim (split_one l); simpl in |- *; auto.
intros H1 H2; case H2.
intros a1 l0 H1 H2 [H3| H3]; auto.
injection H3; intros H4 H5; (rewrite <- H4; rewrite <- H5).
apply permutation_trans with (a :: fst a1 :: snd a1); auto.
apply permutation_skip.
apply H2; auto.
case a1; simpl in |- *; auto.
Qed.

(************************************** 
   All elements of the list are there
   **************************************)
 
Theorem split_one_in_ex :
 forall (a : A) (l1 : list A),
 In a l1 -> exists l2 : list A, In (a, l2) (split_one l1).
intros a l1; elim l1; simpl in |- *; auto.
intros H; case H.
intros a0 l H [H0| H0]; auto.
exists l; left; eq_tac; auto.
case H; auto.
intros x H1; exists (a0 :: x); right; auto.
apply
 (in_map (fun p : A * list A => (fst p, a0 :: snd p)) (split_one l) (a, x));
 auto.
Qed.

(************************************** 
   An auxillary function to generate all permutations
   **************************************)
 
Fixpoint all_permutations_aux (l : list A) (n : nat) {struct n} :
 list (list A) :=
  match n with
  | O => nil :: nil
  | S n1 =>
      flat_map
        (fun p : A * list A =>
         map (cons (fst p)) (all_permutations_aux (snd p) n1)) (
        split_one l)
  end.
(************************************** 
   Generate all the permutations
   **************************************)
 
Definition all_permutations (l : list A) := all_permutations_aux l (length l).
 
(************************************** 
   All the elements of the list are permutations
   **************************************)

Let all_permutations_aux_permutation :
  forall (n : nat) (l1 l2 : list A),
  n = length l2 -> In l1 (all_permutations_aux l2 n) -> permutation l1 l2.
intros n; elim n; simpl in |- *; auto.
intros l1 l2; case l2.
simpl in |- *; intros H0 [H1| H1].
rewrite <- H1; auto.
case H1.
simpl in |- *; intros; discriminate.
intros n0 H l1 l2 H0 H1.
case in_flat_map_ex with (1 := H1).
clear H1; intros x; case x; clear x; intros a1 l3 (H1, H2).
case in_map_inv with (1 := H2).
simpl in |- *; intros y (H3, H4).
rewrite H4; auto.
apply permutation_trans with (a1 :: l3); auto.
apply permutation_skip; auto.
apply H with (2 := H3).
apply eq_add_S.
apply trans_equal with (1 := H0).
change (length l2 = length (a1 :: l3)) in |- *.
apply permutation_length; auto.
apply permutation_sym; apply split_one_permutation; auto.
apply split_one_permutation; auto.
Qed.
 
Theorem all_permutations_permutation :
 forall l1 l2 : list A, In l1 (all_permutations l2) -> permutation l1 l2.
intros l1 l2 H; apply all_permutations_aux_permutation with (n := length l2);
 auto.
Qed.
 
(************************************** 
   A permutation is in the list
   **************************************)

Let permutation_all_permutations_aux :
  forall (n : nat) (l1 l2 : list A),
  n = length l2 -> permutation l1 l2 -> In l1 (all_permutations_aux l2 n).
intros n; elim n; simpl in |- *; auto.
intros l1 l2; case l2.
intros H H0; rewrite permutation_nil_inv with (1 := H0); auto with datatypes.
simpl in |- *; intros; discriminate.
intros n0 H l1; case l1.
intros l2 H0 H1;
 rewrite permutation_nil_inv with (1 := permutation_sym _ _ H1) in H0;
 discriminate.
clear l1; intros a1 l1 l2 H1 H2.
case (split_one_in_ex a1 l2); auto.
apply permutation_in with (1 := H2); auto with datatypes.
intros x H0.
apply in_flat_map with (b := (a1, x)); auto.
apply in_map; simpl in |- *.
apply H; auto.
apply eq_add_S.
apply trans_equal with (1 := H1).
change (length l2 = length (a1 :: x)) in |- *.
apply permutation_length; auto.
apply permutation_sym; apply split_one_permutation; auto.
apply permutation_inv with (a := a1).
apply permutation_trans with (1 := H2).
apply permutation_sym; apply split_one_permutation; auto.
Qed.
 
Theorem permutation_all_permutations :
 forall l1 l2 : list A, permutation l1 l2 -> In l1 (all_permutations l2).
intros l1 l2 H; unfold all_permutations in |- *;
 apply permutation_all_permutations_aux; auto.
Qed.

(************************************** 
   Permutation is decidable
   **************************************)
 
Definition permutation_dec :
  (forall a b : A, {a = b} + {a <> b}) ->
  forall l1 l2 : list A, {permutation l1 l2} + {~ permutation l1 l2}.
intros H l1 l2.
case (In_dec (list_eq_dec H) l1 (all_permutations l2)).
intros i; left; apply all_permutations_permutation; auto.
intros i; right; contradict i; apply permutation_all_permutations; auto.
Defined.
 
End permutation.

(************************************** 
   Hints
   **************************************)

Hint Constructors permutation.
Hint Resolve permutation_refl.
Hint Resolve permutation_app_comp.
Hint Resolve permutation_app_swap.

(************************************** 
   Implicits
   **************************************)

Implicit Arguments permutation [A].
Implicit Arguments split_one [A].
Implicit Arguments all_permutations [A].
Implicit Arguments permutation_dec [A].

(************************************** 
   Permutation is compatible with map
   **************************************)
 
Theorem permutation_map :
 forall (A B : Set) (f : A -> B) l1 l2,
 permutation l1 l2 -> permutation (map f l1) (map f l2).
intros A B f l1 l2 H; elim H; simpl in |- *; auto.
intros l0 l3 l4 H0 H1 H2 H3; apply permutation_trans with (2 := H3); auto.
Qed.
Hint Resolve permutation_map.
 
(************************************** 
  Permutation  of a map can be inverted
  *************************************)

Let permutation_map_ex_aux :
  forall (A B : Set) (f : A -> B) l1 l2 l3,
  permutation l1 l2 ->
  l1 = map f l3 -> exists l4, permutation l4 l3 /\ l2 = map f l4.
intros A1 B1 f l1 l2 l3 H; generalize l3; elim H; clear H l1 l2 l3.
intros l3; case l3; simpl in |- *; auto.
intros H; exists (nil (A:=A1)); auto.
intros; discriminate.
intros a0 l1 l2 H H0 l3; case l3; simpl in |- *; auto.
intros; discriminate.
intros a1 l H1; case (H0 l); auto.
injection H1; auto.
intros l5 (H2, H3); exists (a1 :: l5); split; simpl in |- *; auto.
eq_tac; auto; injection H1; auto.
intros a0 b l l3; case l3.
intros; discriminate.
intros a1 l0; case l0; simpl in |- *.
intros; discriminate.
intros a2 l1 H; exists (a2 :: a1 :: l1); split; simpl in |- *; auto.
repeat eq_tac; injection H; auto.
intros l1 l2 l3 H H0 H1 H2 l0 H3.
case H0 with (1 := H3); auto.
intros l4 (HH1, HH2).
case H2 with (1 := HH2); auto.
intros l5 (HH3, HH4); exists l5; split; auto.
apply permutation_trans with (1 := HH3); auto.
Qed.
 
Theorem permutation_map_ex :
 forall (A B : Set) (f : A -> B) l1 l2,
 permutation (map f l1) l2 ->
 exists l3, permutation l3 l1 /\ l2 = map f l3.
intros A0 B f l1 l2 H; apply permutation_map_ex_aux with (l1 := map f l1);
 auto.
Qed.

(************************************** 
   Permutation is compatible with flat_map
 **************************************)
 
Theorem permutation_flat_map :
 forall (A B : Set) (f : A -> list B) l1 l2,
 permutation l1 l2 -> permutation (flat_map f l1) (flat_map f l2).
intros A B f l1 l2 H; elim H; simpl in |- *; auto.
intros a b l; auto.
repeat rewrite <- app_ass.
apply permutation_app_comp; auto.
intros k3 l4 l5 H0 H1 H2 H3; apply permutation_trans with (1 := H1); auto.
Qed.
