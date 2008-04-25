(********************************************************************)
(*                                                                  *)
(* Micromega: A reflexive tactics using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)

Require Import Setoid.
Require Import Decidable.
Require Import List.
Require Import Refl.

Set Implicit Arguments.

Section CheckerMaker.

(* 'Formula' is a syntactic representation of a certain kind of propositions. *)
Variable Formula : Type.

Variable Env : Type.

Variable eval : Env -> Formula -> Prop.

Variable Formula' : Type.

Variable eval' : Env -> Formula' -> Prop.

Variable normalise : Formula -> Formula'.

Variable negate : Formula -> Formula'.

Hypothesis normalise_sound :
  forall (env : Env) (t : Formula), eval env t -> eval' env (normalise t).

Hypothesis negate_correct :
  forall (env : Env) (t : Formula), eval env t <-> ~ (eval' env (negate t)).

Variable Witness : Type.

Variable check_formulas' : list Formula' -> Witness -> bool.

Hypothesis check_formulas'_sound :
  forall (l : list Formula') (w : Witness),
    check_formulas' l w = true ->
      forall env : Env, make_impl (eval' env) l False.

Definition normalise_list : list Formula -> list Formula' := map normalise.
Definition negate_list : list Formula -> list Formula' := map negate.

Definition check_formulas (l : list Formula) (w : Witness) : bool :=
  check_formulas' (map normalise l) w.

(* Contraposition of normalise_sound for lists *)
Lemma normalise_sound_contr : forall (env : Env) (l : list Formula),
  make_impl (eval' env) (map normalise l) False -> make_impl (eval env) l False.
Proof.
intros env l; induction l as [| t l IH]; simpl in *.
trivial.
intros H1 H2. apply IH. apply H1. now apply normalise_sound.
Qed.

Theorem check_formulas_sound :
  forall (l : list Formula) (w : Witness),
    check_formulas l w = true -> forall env : Env, make_impl (eval env) l False.
Proof.
unfold check_formulas; intros l w H env. destruct l as [| t l]; simpl in *.
pose proof (check_formulas'_sound H env) as H1; now simpl in H1.
intro H1. apply normalise_sound in H1.
pose proof (check_formulas'_sound H env) as H2; simpl in H2.
apply H2 in H1. now apply normalise_sound_contr.
Qed.

(* In check_conj_formulas', t2 is supposed to be a list of negations of
formulas. If, for example, t1 = [A1, A2] and t2 = [~ B1, ~ B2], then
check_conj_formulas' checks that each of [~ B1, A1, A2] and [~ B2, A1, A2] is
inconsistent. This means that A1 /\ A2 -> B1 and A1 /\ A2 -> B1, i.e., that
A1 /\ A2 -> B1 /\ B2. *)

Fixpoint check_conj_formulas'
  (t1 : list Formula') (wits : list Witness) (t2 : list Formula') {struct wits} : bool :=
match t2 with
| nil => true
| t':: rt2 =>
  match wits with
  | nil => false
  | w :: rwits =>
    match check_formulas' (t':: t1) w with
    | true => check_conj_formulas' t1 rwits rt2
    | false => false
    end
  end
end.

(* checks whether the conjunction of t1 implies the conjunction of t2 *)

Definition check_conj_formulas
  (t1 : list Formula) (wits : list Witness) (t2 : list Formula) : bool :=
    check_conj_formulas' (normalise_list t1) wits (negate_list t2).

Theorem check_conj_formulas_sound :
  forall (t1 : list Formula) (t2 : list Formula) (wits : list Witness),
    check_conj_formulas t1 wits t2 = true ->
      forall env : Env, make_impl (eval env) t1 (make_conj (eval env) t2).
Proof.
intro t1; induction t2 as [| a2 t2' IH].
intros; apply make_impl_true.
intros wits H env.
unfold check_conj_formulas in H; simpl in H.
destruct wits as [| w ws]; simpl in H. discriminate.
case_eq (check_formulas' (negate a2 :: normalise_list t1) w);
intro H1; rewrite H1 in H; [| discriminate].
assert (H2 : make_impl (eval' env) (negate a2 :: normalise_list t1) False) by
now apply check_formulas'_sound with (w := w). clear H1.
pose proof (IH ws H env) as H1. simpl in H2.
assert (H3 : eval' env (negate a2) -> make_impl (eval env) t1 False)
by auto using normalise_sound_contr. clear H2.
rewrite <- make_conj_impl in *.
rewrite make_conj_cons. intro H2. split.
apply <- negate_correct. intro; now elim H3. exact (H1 H2).
Qed.

End CheckerMaker.
