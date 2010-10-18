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

Axiom get_make : forall A (a:A) size i, (make size a).[i] = a.
Axiom default_make : forall A (a:A) size, (default (make size a)) = a.

(*** TODO: remove this axiom using get_outofbound, get_set_other *)
Axiom default_set : forall A t i (a:A),
  default (t.[i<-a]) = default t.

Axiom length_make : forall A size (a:A), 
  length (make size a) = if size <= max_array_length then size else max_array_length.
Axiom length_set : forall A t i (a:A),
  length (t.[i<-a]) = length t.

Axiom copy_get : forall A (t:array A) i, (copy t).[i] = t.[i].
Axiom copy_length : forall A (t:array A), length (copy t) = length t.
(*** TODO: remove this axiom using get_outofbound, copy_get *)
Axiom copy_default : forall A (t:array A), default (copy t) = default t.

Axiom reroot_get : forall A (t:array A) i, (reroot t).[i] = t.[i].
Axiom reroot_length : forall A (t:array A), length (copy t) = length t.
(*** TODO: remove this axiom using get_outofbound, reroot_get *)
Axiom reroot_default : forall A (t:array A), default (copy t) = default t.

(* Definition *)
Definition to_list {A:Type} (t:array A) :=
  let len := length t in
  if len == 0 then nil
  else foldi_down (fun i l => t.[i] :: l)%list (len - 1) 0 nil.

Definition forallb {A:Type} (f:A->bool) (t:array A) :=
  forallb (fun i => f (t.[i])) 0 (length t - 1).

Definition existsb {A:Type} (f:A->bool) (t:array A) :=
  existsb (fun i => f (t.[i])) 0 (length t - 1).

Definition mapi {A B:Type} (f:int->A->B) (t:array A) :=
  let size := length t in
  let def := f size (default t) in
  let tb := make size def in
  foldi (fun i tb => tb.[i<- f i (t.[i])]) 0 (size - 1) tb.

Definition map {A B:Type} (f:A->B) :=
  Eval lazy beta delta [mapi] in (mapi (fun i => f)).

Definition foldi_left {A B:Type} (f:int -> A -> B -> A) a (t:array B) :=
  foldi (fun i a => f i a (t.[i])) 0 (length t - 1) a.

Definition fold_left {A B:Type} (f: A -> B -> A) a (t:array B) :=
  foldi (fun i a => f a (t.[i])) 0 (length t - 1) a.

Definition foldi_right {A B:Type} (f:int -> A -> B -> B) (t:array A) b :=
  foldi_down (fun i b => f i (t.[i]) b) (length t - 1) 0 b.

Definition fold_right {A B:Type} (f: A -> B -> B) (t:array A) b :=
  foldi_down (fun i b => f (t.[i]) b) (length t - 1) 0 b.

(* Lemmas *)
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
