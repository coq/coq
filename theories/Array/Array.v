Require Export Int31.

Register array : Type -> Type as array_type.

Register make : forall {A:Type}, int -> A -> array A as array_make.

Register get : forall {A:Type}, array A -> int -> A as array_get.

Register default : forall {A:Type}, array A -> A as array_default.

Register set : forall {A:Type}, array A -> int -> A -> array A as array_set.

Register length : forall {A:Type}, array A -> int as array_length.

Register copy : forall {A:Type}, array A -> array A as array_copy.

Register reroot : forall {A:Type}, array A -> array A as array_reroot.

Delimit Scope array_scope with array.
Notation "t '.[' i ']'" := (get t i) (at level 50) : array_scope.
Notation "t '.[' i '<-' a ']'" := (set t i a) (at level 50) : array_scope.

Local Open Scope int31_scope.
Local Open Scope array_scope.

Set Vm Optimize.

Definition max_array_length := 4194302.

(** Axioms *)
Axiom get_outofbound : forall A (t:array A) i, (i < length t) = false -> t.[i] = default t.

Axiom get_set_same : forall A t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a.
Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
Axiom default_set : forall A t i (a:A), default (t.[i<-a]) = default t.


Axiom get_make : forall A (a:A) size i, (make size a).[i] = a.
Axiom default_make : forall A (a:A) size, (default (make size a)) = a.


Axiom length_make : forall A size (a:A), 
  length (make size a) = if size <= max_array_length then size else max_array_length.
Axiom length_set : forall A t i (a:A),
  length (t.[i<-a]) = length t.

Axiom get_copy : forall A (t:array A) i, (copy t).[i] = t.[i].
Axiom length_copy : forall A (t:array A), length (copy t) = length t.

Axiom get_reroot : forall A (t:array A) i, (reroot t).[i] = t.[i].
Axiom length_reroot : forall A (t:array A), length (reroot t) = length t.

(* Definition *)
Definition to_list {A:Type} (t:array A) :=
  let len := length t in
  if 0 == len then nil
  else foldi_down (fun i l => t.[i] :: l)%list (len - 1) 0 nil.

Definition forallb {A:Type} (f:A->bool) (t:array A) :=
  let len := length t in
  if 0 == len then true
  else forallb (fun i => f (t.[i])) 0 (len - 1).

Definition existsb {A:Type} (f:A->bool) (t:array A) :=
  let len := length t in
  if 0 == len then false
  else existsb (fun i => f (t.[i])) 0 (len - 1).

(* TODO : We should add init as native and add it *)
Definition mapi {A B:Type} (f:int->A->B) (t:array A) :=
  let size := length t in
  let def := f size (default t) in
  let tb := make size def in
  if size == 0 then tb
  else foldi (fun i tb => tb.[i<- f i (t.[i])]) 0 (size - 1) tb.

Definition map {A B:Type} (f:A->B) :=
  Eval lazy beta delta [mapi] in (mapi (fun i => f)).

Definition foldi_left {A B:Type} (f:int -> A -> B -> A) a (t:array B) :=
  let len := length t in
  if 0 == len then a 
  else foldi (fun i a => f i a (t.[i])) 0 (len - 1) a.

Definition fold_left {A B:Type} (f: A -> B -> A) a (t:array B) :=
  let len := length t in
  if 0 == len then a 
  else foldi (fun i a => f a (t.[i])) 0 (length t - 1) a.

Definition foldi_right {A B:Type} (f:int -> A -> B -> B) (t:array A) b :=
  let len := length t in
  if 0 == len then b 
  else foldi_down (fun i b => f i (t.[i]) b) (len - 1) 0 b.

Definition fold_right {A B:Type} (f: A -> B -> B) (t:array A) b :=
  let len := length t in
  if 0 == len then b 
  else foldi_down (fun i b => f (t.[i]) b) (len - 1) 0 b.

(* Lemmas *)

Lemma default_copy : forall A (t:array A), default (copy t) = default t.
Proof.
 intros A t;assert (length t < length t = false).
  apply Bool.not_true_is_false; apply leb_not_gtb; apply leb_refl.
 rewrite <- (get_outofbound _ (copy t) (length t)), <- (get_outofbound _ t (length t)), get_copy;trivial.
 rewrite length_copy;trivial.
Qed.

Lemma reroot_default : forall A (t:array A), default (reroot t) = default t.
Proof.
 intros A t;assert (length t < length t = false).
  apply Bool.not_true_is_false; apply leb_not_gtb; apply leb_refl.
 rewrite <- (get_outofbound _ (reroot t) (length t)), <- (get_outofbound _ t (length t)), get_reroot;trivial.
 rewrite length_reroot;trivial.
Qed.

Lemma get_set_same_default : 
   forall (A : Type) (t : array A) (i : int) ,
       (t .[ i <- default t]) .[ i] = default t.
Proof.
 intros A t i;case_eq (i < (length t));intros.
 rewrite get_set_same;trivial.
 rewrite get_outofbound, default_set;trivial.
 rewrite length_set;trivial.
Qed.

Lemma get_not_default_lt : forall A (t:array A) x,
 t.[x] <> default t -> (x < length t)%int31 = true.
Proof.
 intros A t x Hd.
 case_eq (x < length t);intros Heq;[trivial | ].
 elim Hd;rewrite get_outofbound;trivial.
Qed.

(* Move *)
Lemma leb_negb_gtb : forall x y, x <= y = negb (y < x).
Proof.
 intros x y;apply Bool.eq_true_iff_eq;split;intros.
 apply Bool.eq_true_not_negb;apply leb_not_gtb;trivial.
 rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false in H.
 rewrite leb_spec; rewrite ltb_spec in H;omega.
Qed.

Lemma ltb_negb_geb : forall x y, x < y = negb (y <= x).
Proof.
 intros;rewrite leb_negb_gtb, Bool.negb_involutive;trivial.
Qed.

Lemma fold_left_Ind : 
     forall A B (P : int -> A -> Prop) (f : A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P i a -> P (i+1) (f a (t.[i]))) ->
     forall a, P 0 a ->
     P (length t) (fold_left f a t).
Proof.
 intros;unfold fold_left.
 destruct (reflect_eqb 0 (length t)).
   rewrite <- e; trivial.
 set (P' z := 0 <= z = true -> z < length t = true ->
            forall a, P (length t - 1 - z) a -> 
            P (length t) (foldi (fun (i : int) (a0 : A) => f a0 (t .[ i])) (length t - 1 - z) (length t - 1) a)).
 assert (P' (length t - 1)).
  apply int_ind;unfold P'.
  replace (length t - 1 - 0) with (length t - 1);[ intros| ring].
  assert (length t = length t - 1 + 1) by ring.
  rewrite H4 at 1;rewrite foldi_eq;trivial.
  apply H;trivial. rewrite ltb_spec, to_Z_sub_1;auto with zarith.
  intros.
  rewrite foldi_lt.
  assert (Eq : length t - 1 - (i + 1) + 1 = length t - 1 - i) by ring.
  rewrite Eq;apply H2. apply leb_0.
  assert (W:= to_Z_bounded max_int);rewrite ltb_spec in H1. 
  assert (W1 := to_Z_bounded i); assert (W2 := to_Z_bounded (length t)).
  generalize H4; rewrite !ltb_spec, add_spec, to_Z_1, Zmod_small;try omega.
  rewrite <- Eq;apply H;trivial.
  assert (W:= to_Z_sub_1 (length t) (not_eq_sym n)).
  assert (W1:= to_Z_bounded max_int); assert (W2:= to_Z_bounded i).
  assert ([|i+1|] = [|i|] + 1)%Z.
   rewrite ltb_spec in H1;
   rewrite add_spec, to_Z_1, Zmod_small;auto with zarith.
  rewrite leb_spec in H3;rewrite ltb_spec in H4 |- *.
  assert (W3 := to_Z_bounded (length t)).
  rewrite (sub_spec (length t - 1)), Zmod_small;try omega.
  assert (W:= to_Z_sub_1 (length t) (not_eq_sym n)).
  assert (W1:= to_Z_bounded max_int); assert (W2:= to_Z_bounded i).
  assert ([|i+1|] = [|i|] + 1)%Z.
   rewrite ltb_spec in H1;
   rewrite add_spec, to_Z_1, Zmod_small;auto with zarith.
  rewrite leb_spec in H3;rewrite ltb_spec in H4 |- *.
  assert (W3 := to_Z_bounded (length t)).
  rewrite (sub_spec (length t - 1)), Zmod_small;try omega.
 red in H1;replace (length t - 1 - (length t - 1)) with 0 in H1;[apply H1;trivial | ring ].
 apply leb_0. rewrite ltb_leb_sub1;auto using leb_refl.
Qed.

Lemma fold_left_ind : 
     forall A B (P : A -> Prop) (f : A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P a -> P (f a (t.[i]))) ->
     forall a, P a ->
     P (fold_left f a t).
Proof.
 intros;unfold fold_left.
 case_eq (0 == (length t));intros Heq;trivial.
 apply foldi_ind;trivial.
 cut (0 < length t = true);[ | 
  (generalize (leb_0 (length t));rewrite leb_ltb_eqb, Heq, Bool.orb_false_r;trivial)].
 intros;apply H;trivial.
 rewrite leb_spec in *;rewrite ltb_spec in *. rewrite to_Z_0 in H1.
 assert (W:= to_Z_bounded (length t));rewrite sub_spec, to_Z_1, Zmod_small in H3;omega.
Qed.

Lemma forallb_spec : forall A (f : A -> bool) t,
  forallb f t = true <-> forall i, i < length t = true -> f (t.[i]) = true.
Proof.
 unfold forallb;intros A f t.
 destruct (reflect_eqb 0 (length t)).
 split;[intros | trivial].
 elim (ltb_0 i);rewrite e;trivial.
 rewrite forallb_spec;split;intros Hi i;intros;apply Hi.
 apply leb_0. rewrite <- ltb_leb_sub1;auto. rewrite ltb_leb_sub1;auto.
Qed.

Lemma existsb_spec : forall A (f : A -> bool) t,
  existsb f t = true <-> exists i, i < length t = true /\ f (t.[i]) = true.
Proof.
 unfold existsb;intros A f t.
 destruct (reflect_eqb 0 (length t)).
 split;[discriminate | intros [i [Hi _]];rewrite <- e in Hi;elim (ltb_0 _ Hi)].
 rewrite existsb_spec. repeat setoid_rewrite Bool.andb_true_iff.
 split;intros [i H];decompose [and] H;clear H;exists i;repeat split;trivial.
 rewrite ltb_leb_sub1;auto. apply leb_0. rewrite <- ltb_leb_sub1;auto.
Qed.


