(* Test for evar map consistency - was failing at some point and was *)
(* assumed to be solved from revision 10151 (but using a bad fix) *)

Require Import List.
Set Implicit Arguments.

Inductive rose : Set := Rose : nat -> list rose -> rose.

Section RoseRec.
Variables (P: rose -> Set)(L: list rose -> Set).
Hypothesis
  (R: forall n rs, L rs -> P (Rose n rs))
  (Lnil: L nil)
  (Lcons: forall r rs, P r -> L rs -> L (cons r rs)).

Fixpoint rose_rec2 (t:rose) {struct t} : P t :=
  match t as x return P x with
  | Rose n rs =>
    R n ((fix rs_ind (l' : list rose): L l' :=
         match l' as x return L x with
         | nil => Lnil
         | cons t tl => Lcons (rose_rec2 t) (rs_ind tl)
         end)
         rs)
  end.
End RoseRec.

Lemma rose_map : rose -> rose.
Proof. intro H; elim H using rose_rec2 with
    (L:=fun _ => list rose); (* was assumed to fail here *)
(*  (L:=fun (_:list rose) => list rose); *)
  clear H; simpl; intros.
  exact (Rose n rs). exact nil. exact (H::H0).
Defined.
