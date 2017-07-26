Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Fixpoint tuple' T n : Type :=
  match n with
  | O => T
  | S n' => (tuple' T n' * T)%type
  end.

Definition tuple T n : Type :=
  match n with
  | O => unit
  | S n' => tuple' T n'
  end.

Fixpoint to_list' {T} (n:nat) {struct n} : tuple' T n -> list T :=
  match n with
  | 0 => fun x => (x::nil)%list
  | S n' => fun xs : tuple' T (S n') => let (xs', x) := xs in (x :: to_list' n' xs')%list
  end.

Definition to_list {T} (n:nat) : tuple T n -> list T :=
  match n with
  | 0 => fun _ => nil
  | S n' => fun xs : tuple T (S n') => to_list' n' xs
  end.

Program Fixpoint from_list' {T} (y:T) (n:nat) (xs:list T) : length xs = n -> tuple' T n :=
  match n return _ with
  | 0 =>
    match xs return (length xs = 0 -> tuple' T 0) with
    | nil => fun _ => y
    | _ => _ (* impossible *)
    end
  | S n' =>
    match xs return (length xs = S n' -> tuple' T (S n')) with
    | cons x xs' => fun _ => (from_list' x n' xs' _, y)
    | _ => _ (* impossible *)
    end
  end.
Goal True.
  pose from_list'_obligation_3 as e.
  repeat (let e' := fresh in
          rename e into e';
          (pose (e' nat) as e || pose (e' 0) as e || pose (e' nil) as e || pose (e' eq_refl) as e);
          subst e').
  progress hnf in e.
  pose (eq_refl : e = eq_refl).
  exact I.
Qed.

Program Definition from_list {T} (n:nat) (xs:list T) : length xs = n -> tuple T n :=
match n return _ with
| 0 =>
    match xs return (length xs = 0 -> tuple T 0) with
    | nil => fun _ : 0 = 0 => tt
    | _ => _ (* impossible *)
    end
| S n' =>
    match xs return (length xs = S n' -> tuple T (S n')) with
    | cons x xs' => fun _ => from_list' x n' xs' _
    | _ => _ (* impossible *)
    end
end.

Lemma to_list_from_list : forall {T} (n:nat) (xs:list T) pf, to_list n (from_list n xs pf) = xs.
Proof.
  destruct xs; simpl; intros; subst; auto.
  generalize dependent t. simpl in *.
  induction xs; simpl in *; intros; congruence.
Qed.
