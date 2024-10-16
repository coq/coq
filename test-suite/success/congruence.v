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
