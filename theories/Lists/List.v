  (************************************************************************)
  (*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
  (* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
  (*   \VV/  **************************************************************)
  (*    //   *      This file is distributed under the terms of the       *)
  (*         *       GNU Lesser General Public License Version 2.1        *)
  (************************************************************************)

  (*i $Id$ i*)

Require Import Le Gt Minus Min Bool.

Set Implicit Arguments.


(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** ** Definitions *)

Section Lists.

  Variable A : Type.

  Inductive list : Type :=
    | nil : list
    | cons : A -> list -> list.

  Infix "::" := cons (at level 60, right associativity) : list_scope.

  Open Scope list_scope.

  (** Head and tail        *)
  Definition head (l:list) :=
    match l with
      | nil => error
      | x :: _ => value x
    end.

 Definition hd (default:A) (l:list) :=
   match l with
     | nil => default
     | x :: _ => x
   end. 

  Definition tail (l:list) : list :=
    match l with
      | nil => nil
      | a :: m => m
    end.

  (** Length of lists                *)
  Fixpoint length (l:list) : nat :=
    match l with
      | nil => 0
      | _ :: m => S (length m)
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list) {struct l} : Prop :=
    match l with
      | nil => False
      | b :: m => b = a \/ In a m
    end.


  (** Concatenation of two lists *)
  Fixpoint app (l m:list) {struct l} : list :=
    match l with
      | nil => m
      | a :: l1 => a :: app l1 m
    end.
  
  Infix "++" := app (right associativity, at level 60) : list_scope.
  
End Lists.

(** Exporting list notations and tactics *)

Implicit Arguments nil [A].
Infix "::" := cons (at level 60, right associativity) : list_scope.
Infix "++" := app (right associativity, at level 60) : list_scope.
 
Ltac now_show c := change c in |- *.

Open Scope list_scope.

Delimit Scope list_scope with list.

Bind Scope list_scope with list.

Arguments Scope list [type_scope].

(** ** Facts about lists *)

Section Facts.

  Variable A : Type.


  (** *** Genereric facts *)

  (** Discrimination *)
  Theorem nil_cons : forall (x:A) (l:list A), nil <> x :: l.
  Proof. 
    intros; discriminate.
  Qed.


  (** Destruction *)

  Theorem destruct_list : forall l : list A, {x:A & {tl:list A | l = x::tl}}+{l = nil}.
  Proof.
    induction l as [|a tl].
    right; reflexivity.
    left; exists a; exists tl; reflexivity.
  Qed.
    
  (** *** Head and tail *)
  
  Theorem head_nil : head (@nil A) = None.
  Proof.
    simpl; reflexivity.
  Qed.

  Theorem head_cons : forall (l : list A) (x : A), head (x::l) = Some x.
  Proof.
    intros; simpl; reflexivity.
  Qed.


  (************************)
  (** *** Facts about [In] *) 
  (************************)


  (** Characterization of [In] *)
  
  Theorem in_eq : forall (a:A) (l:list A), In a (a :: l).
  Proof. 
    simpl in |- *; auto.
  Qed.
  
  Theorem in_cons : forall (a b:A) (l:list A), In b l -> In b (a :: l).
  Proof. 
    simpl in |- *; auto.
  Qed.

  Theorem in_nil : forall a:A, ~ In a nil.
  Proof.
    unfold not in |- *; intros a H; inversion_clear H.
  Qed.

  Lemma In_split : forall x (l:list A), In x l -> exists l1, exists l2, l = l1++x::l2.
  Proof.
  induction l; simpl; destruct 1.
  subst a; auto.
  exists (@nil A); exists l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1); exists l2; simpl; f_equal; auto.
  Qed.

  (** Inversion *)
  Theorem in_inv : forall (a b:A) (l:list A), In b (a :: l) -> a = b \/ In b l.
  Proof.
    intros a b l H; inversion_clear H; auto.
  Qed.

  (** Decidability of [In] *)
  Theorem In_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list A), {In a l} + {~ In a l}.
  Proof.
    intro H; induction l as [| a0 l IHl].
    right; apply in_nil.
    destruct (H a0 a); simpl in |- *; auto.
    destruct IHl; simpl in |- *; auto. 
    right; unfold not in |- *; intros [Hc1| Hc2]; auto.
  Defined.


  (*************************)
  (** *** Facts about [app] *)
  (*************************)

  (** Discrimination *)
  Theorem app_cons_not_nil : forall (x y:list A) (a:A), nil <> x ++ a :: y.
  Proof.
    unfold not in |- *.
    destruct x as [| a l]; simpl in |- *; intros.
    discriminate H.
    discriminate H.
  Qed.


  (** Concat with [nil] *)

  Theorem app_nil_end : forall l:list A, l = l ++ nil.
  Proof. 
    induction l; simpl in |- *; auto.
    rewrite <- IHl; auto.
  Qed.

  (** [app] is associative *)
  Theorem app_ass : forall l m n:list A, (l ++ m) ++ n = l ++ m ++ n.
  Proof. 
    intros. induction l; simpl in |- *; auto.
    now_show (a :: (l ++ m) ++ n = a :: l ++ m ++ n).
    rewrite <- IHl; auto.
  Qed.
  Hint Resolve app_ass.

  Theorem ass_app : forall l m n:list A, l ++ m ++ n = (l ++ m) ++ n.
  Proof. 
    auto using app_ass.
  Qed.

  (** [app] commutes with [cons] *) 
  Theorem app_comm_cons : forall (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
  Proof.
    auto.
  Qed.



  (** Facts deduced from the result of a concatenation *)  

  Theorem app_eq_nil : forall l l':list A, l ++ l' = nil -> l = nil /\ l' = nil.
  Proof.
    destruct l as [| x l]; destruct l' as [| y l']; simpl in |- *; auto.
    intro; discriminate.
    intros H; discriminate H.
  Qed.

  Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
    destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ];
      simpl in |- *.
    intros a H; discriminate H.
    left; split; auto.
    right; split; auto.
    generalize H.
    generalize (app_nil_end l); intros E.
    rewrite <- E; auto.
    intros.
    injection H.
    intro.
    cut (nil = l ++ a0 :: l0); auto.
    intro.
    generalize (app_cons_not_nil _ _ _ H1); intro.
    elim H2.
  Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ a :: nil = y ++ b :: nil -> x = y /\ a = b.
  Proof.
    induction x as [| x l IHl];
      [ destruct y as [| a l] | destruct y as [| a l0] ]; 
      simpl in |- *; auto.
    intros a b H.
    injection H.
    auto.
    intros a0 b H.
    injection H; intros.
    generalize (app_cons_not_nil _ _ _ H0); destruct 1.
    intros a b H.
    injection H; intros.
    cut (nil = l ++ a :: nil); auto.
    intro.
    generalize (app_cons_not_nil _ _ _ H2); destruct 1.
    intros a0 b H.
    injection H; intros.
    destruct (IHl l0 a0 b H0). 
    split; auto.
    rewrite <- H1; rewrite <- H2; reflexivity.
  Qed.


  (** Compatibility wtih other operations *)

  Lemma app_length : forall l l' : list A, length (l++l') = length l + length l'.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), In a (l ++ m) -> In a l \/ In a m.
  Proof. 
    intros l m a.
    elim l; simpl in |- *; auto.
    intros a0 y H H0.
    now_show ((a0 = a \/ In a y) \/ In a m).
    elim H0; auto.
    intro H1.
    now_show ((a0 = a \/ In a y) \/ In a m).
    elim (H H1); auto.
  Qed.

  Lemma in_or_app : forall (l m:list A) (a:A), In a l \/ In a m -> In a (l ++ m).
  Proof. 
    intros l m a.
    elim l; simpl in |- *; intro H.
    now_show (In a m).
    elim H; auto; intro H0.
    now_show (In a m).
    elim H0. (* subProof completed *)
    intros y H0 H1.
    now_show (H = a \/ In a (y ++ m)).
    elim H1; auto 4.
    intro H2.
    now_show (H = a \/ In a (y ++ m)).
    elim H2; auto.
  Qed.
  
  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 ->  l1 = l2.
  Proof.
    induction l; simpl; auto; injection 1; auto.
  Qed.
 
  Lemma app_inv_tail:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l ->  l1 = l2.
  Proof.
    intros l l1 l2; revert l1 l2 l.
    induction l1 as [ | x1 l1]; destruct l2 as [ | x2 l2]; 
     simpl; auto; intros l H.
    absurd (length (x2 :: l2 ++ l) <= length l).
    simpl; rewrite app_length; auto with arith.
    rewrite <- H; auto with arith.
    absurd (length (x1 :: l1 ++ l) <= length l).
    simpl; rewrite app_length; auto with arith.
    rewrite H; auto with arith.
    injection H; clear H; intros; f_equal; eauto.
  Qed.

End Facts.

Hint Resolve app_nil_end ass_app app_ass: datatypes v62.
Hint Resolve app_comm_cons app_cons_not_nil: datatypes v62.
Hint Immediate app_eq_nil: datatypes v62.
Hint Resolve app_eq_unit app_inj_tail: datatypes v62. 
Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes v62.



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, nil => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, nil => false
      | S m, x :: t => nth_ok m t default
    end.

  Lemma nth_in_or_default :
    forall (n:nat) (l:list A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
  (* Realizer nth_ok. Program_all. *)
  Proof. 
    intros n l d; generalize n; induction l; intro n0.
    right; case n0; trivial.
    case n0; simpl in |- *.
    auto.
    intro n1; elim (IHl n1); auto.     
  Qed.

  Lemma nth_S_cons :
    forall (n:nat) (l:list A) (d a:A),
      In (nth n l d) l -> In (nth (S n) (a :: l) d) (a :: l).
  Proof. 
    simpl in |- *; auto.
  Qed.

  Fixpoint nth_error (l:list A) (n:nat) {struct n} : Exc A :=
    match n, l with
      | O, x :: _ => value x
      | S n, _ :: l => nth_error l n
      | _, _ => error
    end.

  Definition nth_default (default:A) (l:list A) (n:nat) : A :=
    match nth_error l n with
      | Some x => x
      | None => default
    end.

  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.

  Proof.
    unfold lt in |- *; induction n as [| n hn]; simpl in |- *.
    destruct l; simpl in |- *; [ inversion 2 | auto ].
    destruct l as [| a l hl]; simpl in |- *.
    inversion 2.
    intros d ie; right; apply hn; auto with arith.
  Qed.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof.
    induction l; destruct n; simpl; intros; auto.
    inversion H.
    apply IHl; auto with arith.
  Qed.

  Lemma nth_indep : 
    forall l n d d', n < length l -> nth n l d = nth n l d'.
  Proof.
    induction l; simpl; intros; auto.
    inversion H.
    destruct n; simpl; auto with arith.
  Qed.

  Lemma app_nth1 : 
    forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
  Proof.
    induction l.
    intros.
    inversion H.
    intros l' d n.
    case n; simpl; auto.
    intros; rewrite IHl; auto with arith.
  Qed.

  Lemma app_nth2 : 
    forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
  Proof.
    induction l.
    intros.
    simpl.
    destruct n; auto.
    intros l' d n.
    case n; simpl; auto.
    intros.
    inversion H.
    intros.
    rewrite IHl; auto with arith.
  Qed.




  (*****************)
  (** ** Remove    *)
  (*****************)

  Section Remove.

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.
    
    Fixpoint remove (x : A) (l : list A){struct l} : list A :=
      match l with
	| nil => nil
	| y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
      end.
    
    Theorem remove_In : forall (l : list A) (x : A), ~ In x (remove x l).
    Proof.
      induction l as [|x l]; auto.
      intro y; simpl; destruct (eq_dec y x) as [yeqx | yneqx]. 
      apply IHl.
      unfold not; intro HF; simpl in HF; destruct HF; auto.
      apply (IHl y); assumption. 
    Qed.
  
  End Remove.


(******************************)
(** ** Last element of a list *)
(******************************)

  (** [last l d] returns the last element of the list [l], 
    or the default value [d] if [l] is empty. *)

  Fixpoint last (l:list A) (d:A)  {struct l} : A := 
  match l with 
    | nil => d 
    | a :: nil => a 
    | a :: l => last l d
  end.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list A) {struct l} : list A := 
    match l with 
      | nil =>  nil 
      | a :: nil => nil 
      | a :: l => a :: removelast l
    end.
  
  Lemma app_removelast_last : 
    forall l d, l<>nil -> l = removelast l ++ (last l d :: nil).
  Proof.
    induction l.
    destruct 1; auto.
    intros d _.
    destruct l; auto.
    pattern (a0::l) at 1; rewrite IHl with d; auto; discriminate.
  Qed.
  
  Lemma exists_last : 
    forall l, l<>nil -> { l' : (list A) & { a : A | l = l'++a::nil}}. 
  Proof. 
    induction l.
    destruct 1; auto.
    intros _.
    destruct l.
    exists (@nil A); exists a; auto.
    destruct IHl as [l' (a',H)]; try discriminate.
    rewrite H.
    exists (a::l'); exists a'; auto.
  Qed.

  
  (****************************************)
  (** ** Counting occurences of a element *)
  (****************************************)

  Hypotheses eqA_dec : forall x y : A, {x = y}+{x <> y}.
  
  Fixpoint count_occ (l : list A) (x : A){struct l} : nat :=
    match l with 
      | nil => 0
      | y :: tl => 
	let n := count_occ tl x in 
	  if eqA_dec y x then S n else n
    end.
  
  (** Compatibility of count_occ with operations on list *)
  Theorem count_occ_In : forall (l : list A) (x : A), In x l <-> count_occ l x > 0.
  Proof.
    induction l as [|y l].
    simpl; intros; split; [destruct 1 | apply gt_irrefl].
    simpl. intro x; destruct (eqA_dec y x) as [Heq|Hneq].
    rewrite Heq; intuition. 
    pose (IHl x). intuition.
  Qed.
  
  Theorem count_occ_inv_nil : forall (l : list A), (forall x:A, count_occ l x = 0) <-> l = nil.
  Proof.
    split.
    (* Case -> *)
    induction l as [|x l].
    trivial.
    intro H.
    elim (O_S (count_occ l x)).
    apply sym_eq.
    generalize (H x).
    simpl. destruct (eqA_dec x x) as [|HF].
    trivial.
    elim HF; reflexivity.
    (* Case <- *)
    intro H; rewrite H; simpl; reflexivity.
  Qed.
  
  Lemma count_occ_nil : forall (x : A), count_occ nil x = 0.
  Proof.
    intro x; simpl; reflexivity.
  Qed.

  Lemma count_occ_cons_eq : forall (l : list A) (x y : A), x = y -> count_occ (x::l) y = S (count_occ l y).
  Proof.
    intros l x y H; simpl.
    destruct (eqA_dec x y); [reflexivity | contradiction].
  Qed.
  
  Lemma count_occ_cons_neq : forall (l : list A) (x y : A), x <> y -> count_occ (x::l) y = count_occ l y.
  Proof.
    intros l x y H; simpl.
    destruct (eqA_dec x y); [contradiction | reflexivity]. 
  Qed.

End Elts.



(*******************************)
(** * Manipulating whole lists *)
(*******************************)

Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint rev (l:list A) : list A :=
    match l with
      | nil => nil
      | x :: l' => rev l' ++ x :: nil
    end.

  Lemma distr_rev : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
  Proof.
    induction x as [| a l IHl].
    destruct y as [| a l].
    simpl in |- *.
    auto.

    simpl in |- *.
    apply app_nil_end; auto.

    intro y.
    simpl in |- *.
    rewrite (IHl y).
    apply (app_ass (rev y) (rev l) (a :: nil)).
  Qed.

  Remark rev_unit : forall (l:list A) (a:A), rev (l ++ a :: nil) = a :: rev l.
  Proof.
    intros.
    apply (distr_rev l (a :: nil)); simpl in |- *; auto.
  Qed.

  Lemma rev_involutive : forall l:list A, rev (rev l) = l.
  Proof.
    induction l as [| a l IHl].
    simpl in |- *; auto.

    simpl in |- *.
    rewrite (rev_unit (rev l) a).
    rewrite IHl; auto.
  Qed.


  (** Compatibility with other operations *)

  Lemma In_rev : forall l x, In x l <-> In x (rev l).
  Proof.
    induction l.
    simpl; intuition.
    intros.
    simpl.
    intuition.
    subst.
    apply in_or_app; right; simpl; auto.
    apply in_or_app; left; firstorder.
    destruct (in_app_or _ _ _ H); firstorder.
  Qed.

  Lemma rev_length : forall l, length (rev l) = length l.
  Proof.
    induction l;simpl; auto.
    rewrite app_length.
    rewrite IHl.
    simpl.
    elim (length l); simpl; auto.
  Qed.

  Lemma rev_nth : forall l d n,  n < length l ->  
    nth n (rev l) d = nth (length l - S n) l d.
  Proof.
    induction l.
    intros; inversion H.
    intros.
    simpl in H.
    simpl (rev (a :: l)).
    simpl (length (a :: l) - S n).
    inversion H.
    rewrite <- minus_n_n; simpl.
    rewrite <- rev_length.
    rewrite app_nth2; auto.
    rewrite <- minus_n_n; auto.
    rewrite app_nth1; auto.
    rewrite (minus_plus_simpl_l_reverse (length l) n 1).
    replace (1 + length l) with (S (length l)); auto with arith.
    rewrite <- minus_Sn_m; auto with arith.
    apply IHl ; auto with arith.
    rewrite rev_length; auto.
  Qed.


  (**  An alternative tail-recursive definition for reverse *) 

  Fixpoint rev_append (l l': list A) {struct l} : list A := 
    match l with 
      | nil => l' 
      | a::l => rev_append l (a::l')
    end.

  Definition rev' l : list A := rev_append l nil.

  Notation rev_acc := rev_append (only parsing).

  Lemma rev_append_rev : forall l l', rev_acc l l' = rev l ++ l'.
  Proof.
    induction l; simpl; auto; intros.
    rewrite <- ass_app; firstorder.
  Qed.

  Notation rev_acc_rev := rev_append_rev (only parsing).

  Lemma rev_alt : forall l, rev l = rev_append l nil.
  Proof.
    intros; rewrite rev_append_rev.
    apply app_nil_end.
  Qed.


(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)
  
  Section Reverse_Induction.
    
    Unset Implicit Arguments.
    
    Lemma rev_list_ind :
      forall P:list A-> Prop,
	P nil ->
	(forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
	forall l:list A, P (rev l).
    Proof.
      induction l; auto.
    Qed.
    Set Implicit Arguments.
    
    Theorem rev_ind :
      forall P:list A -> Prop,
	P nil ->
	(forall (x:A) (l:list A), P l -> P (l ++ x :: nil)) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind P).
      auto.
      
      simpl in |- *.
      intros.
      apply (H0 a (rev l0)).
      auto.
    Qed.
  
  End Reverse_Induction.



  (***********************************)
  (** ** Lists modulo permutation    *)
  (***********************************)
  
  Section Permutation.

    Inductive Permutation : list A -> list A -> Prop :=
      | perm_nil: Permutation nil nil
      | perm_skip: forall (x:A) (l l':list A), Permutation l l' -> Permutation (cons x l) (cons x l')
      | perm_swap: forall (x y:A) (l:list A), Permutation (cons y (cons x l)) (cons x (cons y l))
      | perm_trans: forall (l l' l'':list A), Permutation l l' -> Permutation l' l'' -> Permutation l l''.

    Hint Constructors Permutation.

  (** Some facts about [Permutation] *)

    Theorem Permutation_nil : forall (l : list A), Permutation nil l -> l = nil.
    Proof.
      intros l HF.
      set (m:=@nil A) in HF; assert (m = nil); [reflexivity|idtac]; clearbody m.
      induction HF; try elim (nil_cons (sym_eq H)); auto.
    Qed.

    Theorem Permutation_nil_cons : forall (l : list A) (x : A), ~ Permutation nil (x::l).
    Proof.
      unfold not; intros l x HF.
      elim (@nil_cons A x l). apply sym_eq. exact (Permutation_nil HF).
    Qed.

  (** Permutation over lists is a equivalence relation *)

    Theorem Permutation_refl : forall l : list A, Permutation l l.
    Proof.
      induction l; constructor. exact IHl. 
    Qed.

    Theorem Permutation_sym : forall l l' : list A, Permutation l l' -> Permutation l' l.
    Proof.
      intros l l' Hperm; induction Hperm; auto.
      apply perm_trans with (l':=l'); assumption.
    Qed.

    Theorem Permutation_trans : forall l l' l'' : list A, Permutation l l' -> Permutation l' l'' -> Permutation l l''.
    Proof.
      exact perm_trans.
    Qed.

    Hint Resolve Permutation_refl Permutation_sym Permutation_trans.

  (** Compatibility with others operations on lists *)

    Theorem Permutation_in : forall (l l' : list A) (x : A), Permutation l l' -> In x l -> In x l'.
    Proof.
      intros l l' x Hperm; induction Hperm; simpl; tauto. 
    Qed.

    Lemma Permutation_app_tail : forall (l l' tl : list A), Permutation l l' -> Permutation (l++tl) (l'++tl).
    Proof.
      intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; simpl; auto.
      eapply Permutation_trans with (l':=l'++tl); trivial.
    Qed.

    Lemma Permutation_app_head : forall (l tl tl' : list A), Permutation tl tl' -> Permutation (l++tl) (l++tl').
    Proof.
      intros l tl tl' Hperm; induction l; [trivial | repeat rewrite <- app_comm_cons; constructor; assumption].
    Qed.

    Theorem Permutation_app : forall (l m l' m' : list A), Permutation l l' -> Permutation m m' -> Permutation (l++m) (l'++m').
    Proof.
      intros l m l' m' Hpermll' Hpermmm'; induction Hpermll' as [|x l l'|x y l|l l' l'']; repeat rewrite <- app_comm_cons; auto.
      apply Permutation_trans with (l' := (x :: y :: l ++ m));
	[idtac | repeat rewrite app_comm_cons; apply Permutation_app_head]; trivial.
      apply Permutation_trans with (l' := (l' ++ m')); try assumption.
      apply Permutation_app_tail; assumption.
    Qed.

    Theorem Permutation_app_swap : forall (l l' : list A), Permutation (l++l') (l'++l).
    Proof.
      induction l as [|x l]. 
      simpl; intro l'; rewrite <- app_nil_end; trivial.
      induction l' as [|y l'].
      simpl; rewrite <- app_nil_end; trivial.
      simpl; apply Permutation_trans with (l' := x :: y :: l' ++ l).
      constructor; rewrite app_comm_cons; apply IHl.
      apply Permutation_trans with (l' := y :: x :: l' ++ l); constructor.
      apply Permutation_trans with (l' := x :: l ++ l'); auto.
    Qed.
  
    Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
      Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
    Proof.
    intros l l1; revert l.
    induction l1.
    simpl.
    intros; apply perm_skip; auto.
    simpl; intros.
    apply perm_trans with (a0::a::l1++l2).
    apply perm_skip; auto.
    apply perm_trans with (a::a0::l1++l2).
    apply perm_swap; auto.
    apply perm_skip; auto.
    Qed.
    Hint Resolve Permutation_cons_app.

    Theorem Permutation_length : forall (l l' : list A), Permutation l l' -> length l = length l'.
    Proof.
      intros l l' Hperm; induction Hperm; simpl; auto.
      apply trans_eq with (y:= (length l')); trivial.
    Qed.

    Theorem Permutation_rev : forall (l : list A), Permutation l (rev l). 
    Proof.
      induction l as [| x l]; simpl; trivial.
      apply Permutation_trans with (l' := (x::nil)++rev l).
      simpl; auto.
      apply Permutation_app_swap.
    Qed.

    Theorem Permutation_ind_bis : 
     forall P : list A -> list A -> Prop,
       P (@nil A) (@nil A) ->
       (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
       (forall x y l l', Permutation l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
       (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
       forall l l', Permutation l l' -> P l l'.
    Proof.
    intros P Hnil Hskip Hswap Htrans.
    induction 1; auto.
    apply Htrans with (x::y::l); auto.
    apply Hswap; auto.
    induction l; auto.
    apply Hskip; auto.
    apply Hskip; auto.
    induction l; auto.
    eauto.
    Qed.

    Ltac break_list l x l' H := 
     destruct l as [|x l']; simpl in *; 
     injection H; intros; subst; clear H.

    Theorem Permutation_app_inv : forall (l1 l2 l3 l4:list A) a,
      Permutation (l1++a::l2) (l3++a::l4) -> Permutation (l1++l2) (l3 ++ l4).
    Proof.
    set (P:=fun l l' =>  
             forall a l1 l2 l3 l4, l=l1++a::l2 -> l'=l3++a::l4 -> Permutation (l1++l2) (l3++l4)).
    cut (forall l l', Permutation l l' -> P l l').
    intros; apply (H _ _ H0 a); auto.
    intros; apply (Permutation_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto.
    (* nil *)
    intros; destruct l1; simpl in *; discriminate.
    (* skip *)
    intros x l l' H IH; intros.
    break_list l1 b l1' H0; break_list l3 c l3' H1.
    auto.
    apply perm_trans with (l3'++c::l4); auto.
    apply perm_trans with (l1'++a::l2); auto using Permutation_cons_app.
    apply perm_skip.
    apply (IH a l1' l2 l3' l4); auto.
    (* contradict *)
    intros x y l l' Hp IH; intros.
    break_list l1 b l1' H; break_list l3 c l3' H0.
    auto.
    break_list l3' b l3'' H.
    auto.
    apply perm_trans with (c::l3''++b::l4); auto.
    break_list l1' c l1'' H1. 
    auto.
    apply perm_trans with (b::l1''++c::l2); auto.
    break_list l3' d l3'' H; break_list l1' e l1'' H1. 
    auto.
    apply perm_trans with (e::a::l1''++l2); auto.
    apply perm_trans with (e::l1''++a::l2); auto.
    apply perm_trans with (d::a::l3''++l4); auto.
    apply perm_trans with (d::l3''++a::l4); auto.
    apply perm_trans with (e::d::l1''++l2); auto.
    apply perm_skip; apply perm_skip.
    apply (IH a l1'' l2 l3'' l4); auto.
    (*trans*)
    intros.
    destruct (In_split a l') as (l'1,(l'2,H6)).
    apply (Permutation_in a H).
    subst l.
    apply in_or_app; right; red; auto.
    apply perm_trans with (l'1++l'2).
    apply (H0 _ _ _ _ _ H3 H6).
    apply (H2 _ _ _ _ _ H6 H4).
    Qed.

    Theorem Permutation_cons_inv : 
       forall l l' a, Permutation (a::l) (a::l') -> Permutation l l'.
    Proof.
    intros; exact (Permutation_app_inv (@nil _) l (@nil _) l' a H). 
    Qed.

    Theorem Permutation_cons_app_inv :
       forall l l1 l2 a, Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2).
    Proof.
    intros; exact (Permutation_app_inv (@nil _) l l1 l2 a H). 
    Qed.
    
    Theorem Permutation_app_inv_l : 
        forall l l1 l2, Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2.
    Proof.    
    induction l; simpl; auto.
    intros.
    apply IHl.
    apply Permutation_cons_inv with a; auto.
    Qed.

    Theorem Permutation_app_inv_r : 
       forall l l1 l2, Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.
    Proof.
    induction l.
    intros l1 l2; do 2 rewrite <- app_nil_end; auto.
    intros.
    apply IHl.
    apply Permutation_app_inv with a; auto.
    Qed.

  End Permutation.


  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypotheses eqA_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma list_eq_dec :
    forall l l':list A, {l = l'} + {l <> l'}.
  Proof.
    induction l as [| x l IHl]; destruct l' as [| y l'].
    left; trivial.
    right; apply nil_cons. 
    right; unfold not; intro HF; apply (nil_cons (sym_eq HF)).
    destruct (eqA_dec x y) as [xeqy|xneqy]; destruct (IHl l') as [leql'|lneql']; 
      try (right; unfold not; intro HF; injection HF; intros; contradiction).
    rewrite xeqy; rewrite leql'; left; trivial.
  Qed.


End ListOps.


(***************************************************)
(** * Applying functions to the elements of a list *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables A B : Type.
  Variable f : A -> B.
  
  Fixpoint map (l:list A) : list B :=
    match l with
      | nil => nil
      | cons a t => cons (f a) (map t)
    end.
  
  Lemma in_map :
    forall (l:list A) (x:A), In x l -> In (f x) (map l).
  Proof. 
    induction l as [| a l IHl]; simpl in |- *;
      [ auto
	| destruct 1; [ left; apply f_equal with (f := f); assumption | auto ] ].
  Qed.
  
  Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma map_length : forall l, length (map l) = length l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma map_nth : forall l d n, 
    nth n (map l) (f d) = f (nth n l d).
  Proof.
    induction l; simpl map; destruct n; firstorder.
  Qed.
  
  Lemma map_app : forall l l',  
    map (l++l') = (map l)++(map l').
  Proof. 
    induction l; simpl; auto.
    intros; rewrite IHl; auto.
  Qed.
  
  Lemma map_rev : forall l, map (rev l) = rev (map l).
  Proof. 
    induction l; simpl; auto.
    rewrite map_app.
    rewrite IHl; auto.
  Qed.

  Hint Constructors Permutation.

  Lemma Permutation_map : 
    forall l l', Permutation l l' -> Permutation (map l) (map l').
  Proof. 
  induction 1; simpl; auto; eauto.
  Qed.

  (** [flat_map] *)

  Fixpoint flat_map (f:A -> list B) (l:list A) {struct l} : 
    list B :=
    match l with
      | nil => nil
      | cons x t => (f x)++(flat_map f t)
    end.
  
  Lemma in_flat_map : forall (f:A->list B)(l:list A)(y:B),
    In y (flat_map f l) <-> exists x, In x l /\ In y (f x). 
  Proof.
    induction l; simpl; split; intros.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H).
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.

End Map. 

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l, 
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma map_ext : 
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
  induction l; simpl; auto.
  rewrite H; rewrite IHl; auto.
Qed.


(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables A B : Type.
  Variable f : A -> B -> A.
  
  Fixpoint fold_left (l:list B) (a0:A) {struct l} : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.
  
  Lemma fold_left_app : forall (l l':list B)(i:A), 
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof.
    induction l. 
    simpl; auto.
    intros.
    simpl.
    auto.
  Qed.

End Fold_Left_Recursor.

Lemma fold_left_length : 
  forall (A:Type)(l:list A), fold_left (fun x _ => S x) l 0 = length l.
Proof.
  intro A.
  cut (forall (l:list A) n, fold_left (fun x _ => S x) l n = n + length l).
  intros.
  exact (H l 0).
  induction l; simpl; auto.
  intros; rewrite IHl.
  simpl; auto with arith.
Qed.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
  Variables A B : Type.
  Variable f : B -> A -> A.
  Variable a0 : A.
  
  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

  Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i, 
    fold_right f i (l++l') = fold_right f (fold_right f i l') l.
  Proof.
    induction l.
    simpl; auto.
    simpl; intros.
    f_equal; auto.
  Qed.

  Lemma fold_left_rev_right : forall (A B:Type)(f:A->B->B) l i, 
    fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
  Proof.
    induction l.
    simpl; auto.
    intros.
    simpl.
    rewrite fold_right_app; simpl; auto.
  Qed.

  Theorem fold_symmetric :
    forall (A:Type) (f:A -> A -> A),
      (forall x y z:A, f x (f y z) = f (f x y) z) ->
      (forall x y:A, f x y = f y x) ->
      forall (a0:A) (l:list A), fold_left f l a0 = fold_right f a0 l.
  Proof.
    destruct l as [| a l].
    reflexivity.
    simpl in |- *.
    rewrite <- H0.
    generalize a0 a.
    induction l as [| a3 l IHl]; simpl in |- *.
    trivial.
    intros.
    rewrite H.
    rewrite (H0 a2).
    rewrite <- (H a1).
    rewrite (H0 a1).
    rewrite IHl.
    reflexivity.
  Qed.



  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list A) (l':list B) {struct l} :
    list (list (A * B)) :=
    match l with
      | nil => cons nil nil
      | cons x t =>
	flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
        (list_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  Section Bool. 
    Variable A : Type.
    Variable f : A -> bool.

  (** find whether a boolean function can be satisfied by an 
       elements of the list. *)

    Fixpoint existsb (l:list A) {struct l}: bool := 
      match l with 
	| nil => false
	| a::l => f a || existsb l
      end.

    Lemma existsb_exists : 
      forall l, existsb l = true <-> exists x, In x l /\ f x = true.
    Proof.
      induction l; simpl; intuition.
      inversion H.
      firstorder.
      destruct (orb_prop _ _ H1); firstorder.
      firstorder.
      subst.
      rewrite H2; auto.
    Qed.

    Lemma existsb_nth : forall l n d, n < length l ->
      existsb l = false -> f (nth n l d) = false.
    Proof.
      induction l.
      inversion 1.
      simpl; intros.
      destruct (orb_false_elim _ _ H0); clear H0; auto.
      destruct n ; auto. 
      rewrite IHl; auto with arith.
    Qed.

  (** find whether a boolean function is satisfied by 
    all the elements of a list. *)

    Fixpoint forallb (l:list A) {struct l} : bool := 
      match l with 
	| nil => true
	| a::l => f a && forallb l
      end.

    Lemma forallb_forall : 
      forall l, forallb l = true <-> (forall x, In x l -> f x = true).
    Proof.
      induction l; simpl; intuition.
      destruct (andb_prop _ _ H1).
      congruence.
      destruct (andb_prop _ _ H1); auto.
      assert (forallb l = true).
      apply H0; intuition.
      rewrite H1; auto. 
    Qed.

  (** [filter] *)

    Fixpoint filter (l:list A) : list A := 
      match l with 
	| nil => nil
	| x :: l => if f x then x::(filter l) else filter l
      end.

    Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
    Proof.
      induction l; simpl.
      intuition.
      intros.
      case_eq (f a); intros; simpl; intuition congruence.
    Qed.

  (** [find] *)

    Fixpoint find (l:list A) : option A :=
      match l with
	| nil => None
	| x :: tl => if f x then Some x else find tl
      end.

  (** [partition] *)

    Fixpoint partition (l:list A) {struct l} : list A * list A := 
      match l with
	| nil => (nil, nil)
	| x :: tl => let (g,d) := partition tl in 
	  if f x then (x::g,d) else (g,x::d)
      end.

  End Bool.




  (******************************************************)
  (** ** Operations on lists of pairs or lists of lists *)
  (******************************************************)

  Section ListPairs.
    Variables A B : Type.
    
  (** [split] derives two lists from a list of pairs *)

    Fixpoint split  (l:list (A*B)) { struct l }: list A * list B :=
      match l with
	| nil => (nil, nil)
	| (x,y) :: tl => let (g,d) := split tl in (x::g, y::d)
      end.

    Lemma in_split_l : forall (l:list (A*B))(p:A*B), 
      In p l -> In (fst p) (fst (split l)). 
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct H.
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma in_split_r : forall (l:list (A*B))(p:A*B), 
      In p l -> In (snd p) (snd (split l)). 
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct H.
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B), 
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
    Proof.
      induction l.
      destruct n; destruct d; simpl; auto.
      destruct n; destruct d; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
      destruct a; destruct (split l); simpl in *; auto.
      apply IHl.
    Qed.

    Lemma split_length_l : forall (l:list (A*B)),
      length (fst (split l)) = length l. 
    Proof.
      induction l; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

    Lemma split_length_r : forall (l:list (A*B)),
      length (snd (split l)) = length l. 
    Proof.
      induction l; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

  (** [combine] is the opposite of [split]. 
      Lists given to [combine] are meant to be of same length. 
      If not, [combine] stops on the shorter list *)

    Fixpoint combine (l : list A) (l' : list B){struct l} : list (A*B) :=
      match l,l' with
	| x::tl, y::tl' => (x,y)::(combine tl tl')
	| _, _ => nil
      end.

    Lemma split_combine : forall (l: list (A*B)), 
      let (l1,l2) := split l in combine l1 l2 = l.
    Proof.
      induction l.
      simpl; auto.
      destruct a; simpl. 
      destruct (split l); simpl in *.
      f_equal; auto.
    Qed.

    Lemma combine_split : forall (l:list A)(l':list B), length l = length l' -> 
      split (combine l l') = (l,l').
    Proof.
      induction l; destruct l'; simpl; intros; auto; try discriminate.
      injection H; clear H; intros.
      rewrite IHl; auto.
    Qed.

    Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B), 
      In (x,y) (combine l l') -> In x l.
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto; intros.
      contradiction. 
      destruct H.
      injection H; auto.
      right; apply IHl with l' y; auto.
    Qed.

    Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B), 
      In (x,y) (combine l l') -> In y l'.
    Proof.
      induction l.
      simpl; intros; contradiction.
      destruct l'; simpl; auto; intros.
      destruct H.
      injection H; auto.
      right; apply IHl with x; auto.
    Qed.

    Lemma combine_length : forall (l:list A)(l':list B), 
      length (combine l l') = min (length l) (length l').
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto.
    Qed.

    Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B), 
      length l = length l' -> 
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
    Proof.
      induction l; destruct l'; intros; try discriminate.
      destruct n; simpl; auto.
      destruct n; simpl in *; auto.
    Qed.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the 
     same position. *)

    Fixpoint list_prod (l:list A) (l':list B) {struct l} :
      list (A * B) :=
      match l with
	| nil => nil
	| cons x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

    Lemma in_prod_aux :
      forall (x:A) (y:B) (l:list B),
	In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
    Proof. 
      induction l;
	[ simpl in |- *; auto
	  | simpl in |- *; destruct 1 as [H1| ];
	    [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
	In x l -> In y l' -> In (x, y) (list_prod l l').
    Proof. 
      induction l;
	[ simpl in |- *; tauto
	  | simpl in |- *; intros; apply in_or_app; destruct H;
	    [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma in_prod_iff : 
      forall (l:list A)(l':list B)(x:A)(y:B), 
	In (x,y) (list_prod l l') <-> In x l /\ In y l'.
    Proof.
      split; [ | intros; apply in_prod; intuition ].
      induction l; simpl; intros.
      intuition.
      destruct (in_app_or _ _ _ H); clear H.
      destruct (in_map_iff (fun y : B => (a, y)) l' (x,y)) as (H1,_).
      destruct (H1 H0) as (z,(H2,H3)); clear H0 H1.
      injection H2; clear H2; intros; subst; intuition.
      intuition.
    Qed. 

    Lemma prod_length : forall (l:list A)(l':list B), 
      length (list_prod l l') = (length l) * (length l').
    Proof.
      induction l; simpl; auto.
      intros.
      rewrite app_length.
      rewrite map_length.
      auto.
    Qed.

  End ListPairs.




(***************************************)
(** * Miscelenous operations on lists  *)
(***************************************)



(******************************)
(** ** Length order of lists  *)
(******************************)

Section length_order.
  Variable A : Type.

  Definition lel (l m:list A) := length l <= length m.

  Variables a b : A.
  Variables l m n : list A.

  Lemma lel_refl : lel l l.
  Proof. 
    unfold lel in |- *; auto with arith.
  Qed.

  Lemma lel_trans : lel l m -> lel m n -> lel l n.
  Proof. 
    unfold lel in |- *; intros.
    now_show (length l <= length n).
    apply le_trans with (length m); auto with arith.
  Qed.

  Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
  Proof. 
    unfold lel in |- *; simpl in |- *; auto with arith.
  Qed.

  Lemma lel_cons : lel l m -> lel l (b :: m).
  Proof. 
    unfold lel in |- *; simpl in |- *; auto with arith.
  Qed.

  Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
  Proof. 
    unfold lel in |- *; simpl in |- *; auto with arith.
  Qed.

  Lemma lel_nil : forall l':list A, lel l' nil -> nil = l'.
  Proof. 
    intro l'; elim l'; auto with arith.
    intros a' y H H0.
    now_show (nil = a' :: y).
    absurd (S (length y) <= 0); auto with arith.
  Qed.
End length_order.

Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes v62.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl (l m:list A) := forall a:A, In a l -> In a m.
  Hint Unfold incl.
  
  Lemma incl_refl : forall l:list A, incl l l.
  Proof. 
    auto.
  Qed.
  Hint Resolve incl_refl.
  
  Lemma incl_tl : forall (a:A) (l m:list A), incl l m -> incl l (a :: m).
  Proof. 
    auto with datatypes.
  Qed.
  Hint Immediate incl_tl.

  Lemma incl_tran : forall l m n:list A, incl l m -> incl m n -> incl l n.
  Proof. 
    auto.
  Qed.
  
  Lemma incl_appl : forall l m n:list A, incl l n -> incl l (n ++ m).
  Proof. 
    auto with datatypes.
  Qed.
  Hint Immediate incl_appl.
  
  Lemma incl_appr : forall l m n:list A, incl l n -> incl l (m ++ n).
  Proof. 
    auto with datatypes.
  Qed.
  Hint Immediate incl_appr.
  
  Lemma incl_cons :
    forall (a:A) (l m:list A), In a m -> incl l m -> incl (a :: l) m.
  Proof. 
    unfold incl in |- *; simpl in |- *; intros a l m H H0 a0 H1.
    now_show (In a0 m).
    elim H1.
    now_show (a = a0 -> In a0 m).
    elim H1; auto; intro H2.
    now_show (a = a0 -> In a0 m).
    elim H2; auto. (* solves subgoal *)
    now_show (In a0 l -> In a0 m).
    auto.
  Qed.
  Hint Resolve incl_cons.
  
  Lemma incl_app : forall l m n:list A, incl l n -> incl m n -> incl (l ++ m) n.
  Proof. 
    unfold incl in |- *; simpl in |- *; intros l m n H H0 a H1.
    now_show (In a n).
    elim (in_app_or _ _ _ H1); auto.
  Qed.
  Hint Resolve incl_app.
  
End SetIncl.

Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
  incl_app: datatypes v62.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Fixpoint firstn (n:nat)(l:list A) {struct n} : list A := 
    match n with 
      | 0 => nil 
      | S n => match l with  
		 | nil => nil 
		 | a::l => a::(firstn n l)
	       end
    end.
  
  Fixpoint skipn (n:nat)(l:list A) { struct n } : list A := 
    match n with 
      | 0 => l 
      | S n => match l with 
		 | nil => nil 
		 | a::l => skipn n l
	       end
    end.
  
  Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
  Proof.
    induction n.
    simpl; auto.
    destruct l; simpl; auto.
    f_equal; auto.
  Qed.

End Cutting.


(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.
  
  Inductive NoDup : list A -> Prop := 
    | NoDup_nil : NoDup nil 
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l). 

  Lemma NoDup_remove_1 : forall l l' a, NoDup (l++a::l') -> NoDup (l++l').
  Proof.
  induction l; simpl.
  inversion_clear 1; auto.
  inversion_clear 1.
  constructor.
  contradict H0.
  apply in_or_app; destruct (in_app_or _ _ _ H0); simpl; tauto.
  apply IHl with a0; auto.
  Qed.

  Lemma NoDup_remove_2 : forall l l' a, NoDup (l++a::l') -> ~In a (l++l').
  Proof.
  induction l; simpl.
  inversion_clear 1; auto.
  inversion_clear 1.
  contradict H0.
  destruct H0.
  subst a0.
  apply in_or_app; right; red; auto.
  destruct (IHl _ _ H1); auto.
  Qed.

  Lemma NoDup_Permutation : forall l l', 
    NoDup l -> NoDup l' -> (forall x, In x l <-> In x l') -> Permutation l l'.
  Proof.
  induction l. 
  destruct l'; simpl; intros.
  apply perm_nil.
  destruct (H1 a) as (_,H2); destruct H2; auto.
  intros.
  destruct (In_split a l') as (l'1,(l'2,H2)).
  destruct (H1 a) as (H2,H3); simpl in *; auto.
  subst l'.
  apply Permutation_cons_app.
  inversion_clear H.
  apply IHl; auto.
  apply NoDup_remove_1 with a; auto.
  intro x; split; intros.
  assert (In x (l'1++a::l'2)).
   destruct (H1 x); simpl in *; auto.
  apply in_or_app; destruct (in_app_or _ _ _ H4); auto.
  destruct H5; auto.
  subst x; destruct H2; auto.
  assert (In x (l'1++a::l'2)).
    apply in_or_app; destruct (in_app_or _ _ _ H); simpl; auto.
  destruct (H1 x) as (_,H5); destruct H5; auto. 
  subst x.
  destruct (NoDup_remove_2 _ _ _ H0 H).
  Qed.

End ReDun.


(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers 
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)
  
  Fixpoint seq (start len:nat) {struct len} : list nat := 
    match len with 
      | 0 => nil
      | S len => start :: seq (S start) len
    end. 
  
  Lemma seq_length : forall len start, length (seq start len) = len.
  Proof.
    induction len; simpl; auto.
  Qed.
  
  Lemma seq_nth : forall len start n d, 
    n < len -> nth n (seq start len) d = start+n.
  Proof.
    induction len; intros.
    inversion H.
    simpl seq.
    destruct n; simpl.
    auto with arith.
    rewrite IHlen;simpl; auto with arith.
  Qed.

  Lemma seq_shift : forall len start,
    map S (seq start len) = seq (S start) len.
  Proof. 
    induction len; simpl; auto.
    intros.
    rewrite IHlen.
    auto with arith.
  Qed.

End NatSeq.



  (** * Exporting hints and tactics *)


Hint Rewrite 
  rev_involutive (* rev (rev l) = l *)
  rev_unit (* rev (l ++ a :: nil) = a :: rev l *)
  map_nth (* nth n (map f l) (f d) = f (nth n l d) *)
  map_length (* length (map f l) = length l *)
  seq_length (* length (seq start len) = len *)
  app_length (* length (l ++ l') = length l + length l' *)
  rev_length (* length (rev l) = length l *)
  : list.

Hint Rewrite <- 
  app_nil_end (* l = l ++ nil *)
  : list.

Ltac simpl_list := autorewrite with list.
Ltac ssimpl_list := autorewrite with list using simpl.
