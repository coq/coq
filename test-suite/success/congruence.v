Inductive Inner : Type :=
| innerI_nat : forall (x:nat), Inner
| innerI_fun : forall (f:nat->Type), Inner
| innerI_inner : forall (i:Inner), Inner
| innerI_Type : forall (T:Type), Inner
| innerI_extra : Inner.

Inductive ExtractTest (A:Type) (F:nat->Type) (I:Inner): Inner -> Inner -> unit -> Type :=
| extract_f_x_from_index : forall (x:nat) (f:nat->Type) (t:f x),
    ExtractTest A F I (innerI_inner (innerI_nat x)) (innerI_fun f) tt
| extract_F_from_param_x_from_index : forall (x:nat) (f:nat->Type) (t:F x),
    ExtractTest A F I (innerI_inner (innerI_nat x)) innerI_extra tt
| extract_fail : forall (x y: nat) (f : nat -> Type) (t : f x),
    ExtractTest A F I (innerI_nat y) (innerI_fun f) tt
| extract_fx_from_index : forall (x:nat) (f:nat->Type) (t:f x),
    ExtractTest A F I (innerI_Type (f x)) innerI_extra tt
| extract_t_match : forall (b:bool) (t:if b then unit else nat),
    ExtractTest A F I (innerI_Type (if b then unit else nat)) innerI_extra tt
.

Set Debug "dependent_congruence".

Lemma test_extract_f_x_from_index A F x f t1 t2 : extract_f_x_from_index A F innerI_extra x f t1 = extract_f_x_from_index A F innerI_extra x f t2 -> t1 = t2.
Proof.
    intros H.
    congruence.
Qed.

Lemma test_extract_F_from_param_x_from_index A F x f t1 t2 : extract_F_from_param_x_from_index A F innerI_extra x f t1 = extract_F_from_param_x_from_index A F innerI_extra x f t2 -> t1 = t2.
Proof.
    intros H.
    congruence.
Qed.

Lemma test_extract_fx_from_index A F x f t1 t2 :
extract_fx_from_index A F innerI_extra x f t1 = extract_fx_from_index A F innerI_extra x f t2 -> t1 = t2.
Proof.
    intros H.
    congruence.
Qed.

Require Import Vector.

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Lemma test_vec_eq (A:Type) (x:A) (n:nat) (v v' : Vector.t A n) : (x::v = x::v') -> v = v'.
Proof.
    congruence.
Qed.

Require Import Fin.

Lemma test_fin_eq (n:nat) (f f': Fin.t n) : FS f = FS f' -> f = f'.
Proof.
    congruence.
Qed.

Record R (A : Type) (B : A -> Type) : Type := RI { a : A; b : B a }.

Goal forall A B (x : A) (y1 y2 : B),
  y1 <> y2 -> RI _ _ x y1 <> RI _ _ x y2.
Proof.
  intros.
  congruence.
Qed.


Inductive wrap1 (X : unit -> Type) : unit -> forall (v : unit), X v -> Type :=
  | wrap1_zero (x : X tt) : wrap1 X tt tt x
  | wrap1_succ u v x : wrap1 X u v x -> wrap1 X u v x.

Lemma test_wrap1 (x y : unit) (p q : wrap1 (fun _ : unit => unit) tt y x) :
  wrap1_succ (fun _ => unit) tt y x p = wrap1_succ (fun _ => unit) tt y x q -> p = q.
Proof.
  congruence.
Qed.

Inductive wrap2 (X : unit -> Type) : unit -> forall (v : unit), X tt -> Type :=
  | wrap2_zero (x : X tt) : wrap2 X tt tt x
  | wrap2_succ u v x : wrap2 X u v x -> wrap2 X u v x.

Lemma test_wrap2 (y : unit) (X : unit -> Type) (x : X tt) (p q : wrap2 X tt y x) :
  wrap2_succ X tt y x p = wrap2_succ X tt y x q -> p = q.
Proof.
  congruence.
Qed.
