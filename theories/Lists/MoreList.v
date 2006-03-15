(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: MoreList.v,v 1.4 2006/03/13 04:59:24 letouzey Exp $ *)

(** This file contains some complements to [List.v], in particular
  results about lengths of the different lists operations (but not only)
*)

Require Export List.
Require Import Arith.
Require Import Bool.
Set Implicit Arguments.
Unset Strict Implicit.

Section MoreLists.

Variable A B C:Set.

Implicit Types l : list A.


Section Nth.

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

End Nth.

Section App.

Lemma app_length : forall l l', length (l++l') = length l + length l'.
Proof.
induction l; simpl; auto.
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
rewrite <- minus_n_O; auto.
intros l' d n.
case n; simpl; auto.
intros.
inversion H.
intros.
rewrite IHl; auto with arith.
Qed.

End App. 

Section Fold.

Lemma fold_left_length : 
 forall l, fold_left (fun x _ => S x) l 0 = length l.
Proof.
cut (forall l n, fold_left (fun x _ => S x) l n = n + length l).
intros.
exact (H l 0).
induction l; simpl; auto.
intros; rewrite IHl.
simpl; auto with arith.
Qed.

Lemma fold_left_app : forall (l l':list B)(f : A -> B -> A)(i:A), 
 fold_left f (l++l') i = fold_left f l' (fold_left f l i).
Proof.
induction l. 
simpl; auto.
intros.
simpl.
auto.
Qed.

Lemma fold_right_app : forall l l' (f:A->B->B)(i:B), 
  fold_right f i (l++l') = fold_right f (fold_right f i l') l.
Proof.
induction l.
simpl; auto.
simpl; intros.
f_equal; auto.
Qed.

Lemma fold_left_rev_right : forall l (f:A->B->B)(i:B), 
  fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
Proof.
induction l.
simpl; auto.
intros.
simpl.
rewrite fold_right_app; simpl.
auto.
Qed.

End Fold.

Section Rev.

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
simpl; rewrite plus_comm; auto.
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
rewrite <- minus_Sn_m; auto with arith; simpl.
apply IHl; auto.
rewrite rev_length; auto.
Qed.

End Rev.

Section Rev_acc.

(** An alternative tail-recursive definition of [rev] *)

Fixpoint rev_acc (l l': list A) {struct l} : list A := 
 match l with 
  | nil => l' 
  | a::l => rev_acc l (a::l')
 end.

Lemma rev_acc_rev : forall l l', rev_acc l l' = rev l ++ l'.
Proof.
induction l; simpl; auto; intros.
rewrite <- ass_app; firstorder.
Qed.

Lemma rev_alt : forall l, rev l = rev_acc l nil.
Proof.
intros; rewrite rev_acc_rev.
apply app_nil_end.
Qed.

End Rev_acc.

Section Seq. 

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

End Seq.

Section Map.

Variable f : A-> B.

Lemma In_map : forall l y, In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
induction l; firstorder (subst; auto).
Qed.

Lemma map_length : forall l, length (map f l) = length l.
Proof.
induction l; simpl; auto.
Qed.

Lemma map_nth : forall l d n, 
 nth n (map f l) (f d) = f (nth n l d).
Proof.
induction l; simpl map; destruct n; firstorder.
Qed.

Lemma map_app : forall l l',  
 map f (l++l') = (map f l) ++ (map f l').
Proof. 
induction l; simpl; auto.
intros; rewrite IHl; auto.
Qed.

Lemma map_rev : forall l, map f (rev l) = rev (map f l).
Proof. 
induction l; simpl; auto.
rewrite map_app.
rewrite IHl; auto.
Qed.

Lemma map_map : forall (f:A->B)(g:B->C) l, 
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma map_ext : 
 forall g, (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
induction l; simpl; auto.
rewrite H; rewrite IHl; auto.
Qed.

End Map.

Section SplitLast. 

(** [last l d] returns the last elements of the list [l], 
    or the default value [d] if [l] is empty. *)

Fixpoint last (l:list A)(d:A)  {struct l} : A := 
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
 forall l, l<>nil -> { l' : list A & { a : A | l = l'++a::nil}}. 
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

End SplitLast.

Section SplitN. 

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

End SplitN.

Section Bool. 

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

Fixpoint find (l:list A) : option A :=
  match l with
    | nil => None
    | x :: tl => if f x then Some x else find tl
  end.

Fixpoint partition (l:list A) {struct l} : list A * list A := 
  match l with
    | nil => (nil, nil)
    | x :: tl => let (g,d) := partition tl in 
      if f x then (x::g,d) else (g,x::d)
  end.

End Bool.

Section Split.

Fixpoint split  (l:list (A*B)) : list A * list B :=
  match l with
    | nil => (nil, nil)
    | (x,y) :: tl => let (g,d) := split tl in (x::g, y::d)
  end.

(** [combine] stops on the shorter list *)
Fixpoint combine (l : list A) (l' : list B){struct l} : list (A*B) :=
  match l,l' with
    | x::tl, y::tl' => (x,y)::(combine tl tl')
    | _, _ => nil
  end.

End Split.

Section Remove.

Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

Fixpoint remove (x : A) (l : list A){struct l} : list A :=
  match l with
    | nil => nil
    | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
  end.

End Remove.


End MoreLists.

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
