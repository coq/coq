(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*  Library about sorted (sub-)arrays / Nicolas Magaud, July 1998 *)

(* $Id$ *)

Require Export Arrays.
Require Import ArrayPermut.

Require Import ZArithRing.
Require Import Omega.
Open Local Scope Z_scope.

Set Implicit Arguments.

(* Definition *)

Definition sorted_array (N:Z) (A:array N Z) (deb fin:Z) :=
  deb <= fin -> forall x:Z, x >= deb -> x < fin -> #A [x] <= #A [x + 1].

(* Elements of a sorted sub-array are in increasing order *)

(* one element and the next one *)

Lemma sorted_elements_1 :
 forall (N:Z) (A:array N Z) (n m:Z),
   sorted_array A n m ->
   forall k:Z,
     k >= n -> forall i:Z, 0 <= i -> k + i <= m -> #A [k] <= #A [k + i].
Proof.
intros N A n m H_sorted k H_k i H_i.
pattern i in |- *. apply natlike_ind.
intro.
replace (k + 0) with k; omega. (*** Ring `k+0` => BUG ***)

intros.
apply Zle_trans with (m := #A [k + x]).
apply H0; omega.

unfold Zsucc in |- *.
replace (k + (x + 1)) with (k + x + 1).
unfold sorted_array in H_sorted.
apply H_sorted; omega.

omega.

assumption.
Qed.

(* one element and any of the following *)

Lemma sorted_elements :
 forall (N:Z) (A:array N Z) (n m k l:Z),
   sorted_array A n m ->
   k >= n -> l < N -> k <= l -> l <= m -> #A [k] <= #A [l].
Proof.
intros.
replace l with (k + (l - k)).
apply sorted_elements_1 with (n := n) (m := m);
 [ assumption | omega | omega | omega ].
omega.
Qed.

Hint Resolve sorted_elements: datatypes v62.

(* A sub-array of a sorted array is sorted *)

Lemma sub_sorted_array :
 forall (N:Z) (A:array N Z) (deb fin i j:Z),
   sorted_array A deb fin ->
   i >= deb -> j <= fin -> i <= j -> sorted_array A i j.
Proof.
unfold sorted_array in |- *.
intros.
apply H; omega.
Qed.

Hint Resolve sub_sorted_array: datatypes v62.

(* Extension on the left of the property of being sorted *)

Lemma left_extension :
 forall (N:Z) (A:array N Z) (i j:Z),
   i > 0 ->
   j < N ->
   sorted_array A i j -> #A [i - 1] <= #A [i] -> sorted_array A (i - 1) j.
Proof.
intros; unfold sorted_array in |- *; intros.
elim (Z_ge_lt_dec x i).   (* (`x >= i`) + (`x < i`) *)
intro Hcut.
apply H1; omega.

intro Hcut.
replace x with (i - 1).
replace (i - 1 + 1) with i; [ assumption | omega ].

omega.
Qed.

(* Extension on the right *)

Lemma right_extension :
 forall (N:Z) (A:array N Z) (i j:Z),
   i >= 0 ->
   j < N - 1 ->
   sorted_array A i j -> #A [j] <= #A [j + 1] -> sorted_array A i (j + 1).
Proof.
intros; unfold sorted_array in |- *; intros.
elim (Z_lt_ge_dec x j).
intro Hcut. 
apply H1; omega.

intro HCut.
replace x with j; [ assumption | omega ].
Qed.

(* Substitution of the leftmost value by a smaller value *) 

Lemma left_substitution :
 forall (N:Z) (A:array N Z) (i j v:Z),
   i >= 0 ->
   j < N ->
   sorted_array A i j -> v <= #A [i] -> sorted_array (store A i v) i j.
Proof.
intros N A i j v H_i H_j H_sorted H_v.
unfold sorted_array in |- *; intros.

cut (x = i \/ x > i).
intro Hcut; elim Hcut; clear Hcut; intro.
rewrite H2.
rewrite store_def_1; try omega.
rewrite store_def_2; try omega.
apply Zle_trans with (m := #A [i]); [ assumption | apply H_sorted; omega ].

rewrite store_def_2; try omega.
rewrite store_def_2; try omega.
apply H_sorted; omega.
omega.
Qed.

(* Substitution of the rightmost value by a larger value *)

Lemma right_substitution :
 forall (N:Z) (A:array N Z) (i j v:Z),
   i >= 0 ->
   j < N ->
   sorted_array A i j -> #A [j] <= v -> sorted_array (store A j v) i j.
Proof.
intros N A i j v H_i H_j H_sorted H_v.
unfold sorted_array in |- *; intros.

cut (x = j - 1 \/ x < j - 1).
intro Hcut; elim Hcut; clear Hcut; intro.
rewrite H2.
replace (j - 1 + 1) with j; [ idtac | omega ]. (*** Ring `j-1+1`. => BUG ***)
rewrite store_def_2; try omega.
rewrite store_def_1; try omega.
apply Zle_trans with (m := #A [j]). 
apply sorted_elements with (n := i) (m := j); try omega; assumption.
assumption.

rewrite store_def_2; try omega.
rewrite store_def_2; try omega.
apply H_sorted; omega.

omega.
Qed.

(* Affectation outside of the sorted region *)

Lemma no_effect :
 forall (N:Z) (A:array N Z) (i j k v:Z),
   i >= 0 ->
   j < N ->
   sorted_array A i j ->
   0 <= k < i \/ j < k < N -> sorted_array (store A k v) i j.
Proof.
intros.
unfold sorted_array in |- *; intros. 
rewrite store_def_2; try omega.
rewrite store_def_2; try omega.
apply H1; assumption.
Qed.

Lemma sorted_array_id :
 forall (N:Z) (t1 t2:array N Z) (g d:Z),
   sorted_array t1 g d -> array_id t1 t2 g d -> sorted_array t2 g d.
Proof.
intros N t1 t2 g d Hsorted Hid.
unfold array_id in Hid.
unfold sorted_array in Hsorted. unfold sorted_array in |- *.
intros Hgd x H1x H2x.
rewrite <- (Hid x); [ idtac | omega ].
rewrite <- (Hid (x + 1)); [ idtac | omega ].
apply Hsorted; assumption.
Qed.