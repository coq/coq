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

Axiom ltb_length : forall A (t:array A), length t <= max_array_length = true.

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

Lemma foldi_left_Ind : 
     forall A B (P : int -> A -> Prop) (f : int -> A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P i a -> P (i+1) (f i a (t.[i]))) ->
     forall a, P 0 a ->
     P (length t) (foldi_left f a t).
Proof.
 intros;unfold foldi_left.
 destruct (reflect_eqb 0 (length t)).
  rewrite <- e;trivial.
 assert ((length t - 1) + 1 = length t) by ring.
 rewrite <- H1 at 1;apply foldi_Ind;auto.
 assert (W:= leb_max_int (length t));rewrite leb_spec in W.
 rewrite ltb_spec, to_Z_sub_1_diff;auto with zarith.
 intros Hlt;elim (ltb_0 _ Hlt).
 intros;apply H;trivial. rewrite ltb_leb_sub1;auto.
Qed.

Lemma fold_left_Ind : 
     forall A B (P : int -> A -> Prop) (f : A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P i a -> P (i+1) (f a (t.[i]))) ->
     forall a, P 0 a ->
     P (length t) (fold_left f a t).
Proof.
 intros.
 apply (foldi_left_Ind A B P (fun i => f));trivial.
Qed.

Lemma fold_left_ind : 
     forall A B (P : A -> Prop) (f : A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P a -> P (f a (t.[i]))) ->
     forall a, P a ->
     P (fold_left f a t).
Proof.
 intros;apply (fold_left_Ind A B (fun _ => P));trivial.
Qed.

Lemma foldi_right_Ind : 
     forall A B (P : int -> A -> Prop) (f : int -> B -> A -> A) (t:array B),
     (forall a i, i < length t = true -> P (i+1) a -> P i (f i (t.[i]) a)) ->
     forall a, P (length t) a ->
     P 0 (foldi_right f t a).
Proof.
 intros;unfold foldi_right.
 destruct (reflect_eqb 0 (length t)).
  rewrite e;trivial.
 set (P' z a := (*-1 <= z < [|length t|] ->*) P (of_Z (z + 1)) a).
 assert (P' ([|0|] - 1)%Z (foldi_down (fun (i : int) (b : A) => f i (t .[ i]) b) (length t - 1) 0 a)).
 apply foldi_down_ZInd;unfold P'.
 intros Hlt;elim (ltb_0 _ Hlt).
 rewrite to_Z_sub_1_diff;auto.
 ring_simplify ([|length t|] - 1 + 1)%Z;rewrite of_to_Z;trivial.
 intros;ring_simplify ([|i|] - 1 + 1)%Z;rewrite of_to_Z;auto.
 assert (i < length t = true).
   rewrite ltb_leb_sub1;auto.
 apply H;trivial.
 rewrite <-(to_Z_add_1 _ _ H4), of_to_Z in H3;auto.
 exact H1.
Qed.
 
Lemma fold_right_Ind : 
     forall A B (P : int -> A -> Prop) (f : B -> A -> A) (t:array B),
     (forall a i, i < length t = true -> P (i+1) a -> P i (f (t.[i]) a)) ->
     forall a, P (length t) a ->
     P 0 (fold_right f t a).
Proof.
 intros;apply (foldi_right_Ind A B P (fun i => f));trivial.
Qed.

Lemma fold_right_ind : 
     forall A B (P : A -> Prop) (f : B -> A -> A) (t:array B),
     (forall a i, i < length t = true -> P a -> P (f (t.[i]) a)) ->
     forall a, P a ->
     P (fold_right f t a).
Proof.
 intros;apply (fold_right_Ind A B (fun i => P));trivial.
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


