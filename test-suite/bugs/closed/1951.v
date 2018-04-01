
(* First a simplification of the bug *)

Set Printing Universes.

Inductive enc (A:Type (*1*)) (* : Type.1 *) := C : A -> enc A.

Definition id (X:Type(*4*)) (x:X) := x.

Lemma test : let S := Type(*5 : 6*) in enc S -> S.
simpl; intros.
refine (enc _).
apply id.
apply Prop.
Defined.

(* Then the original bug *)

Require Import List.

Inductive a : Set := (* some dummy inductive *)
b : (list a) -> a.   (* i don't know if this *)
                     (* happens for smaller  *)
                     (* ones                 *)

Inductive sg : Type := Sg. (* single *)

Definition ipl2 (P : a -> Type) :=   (* in Prop, that means P is true forall *)
  fold_right (fun x => fun A => prod (P x) A) sg. (* the elements of a given list         *)

Definition ind
     : forall S : a -> Type,
       (forall ls : list a, ipl2 S ls -> S (b ls)) -> forall s : a, S s :=
fun (S : a -> Type)
  (X : forall ls : list a, ipl2 S ls -> S (b ls)) =>
fix ind2 (s : a) :=
match s as a return (S a) with
| b l =>
    X l
      (list_rect (fun l0 : list a => ipl2 S l0) Sg
         (fun (a0 : a) (l0 : list a) (IHl : ipl2 S l0) =>
          pair (ind2 a0) IHl) l)
end. (* some induction principle *)

Arguments ind [S].

Lemma k : a -> Type. (* some ininteresting lemma *)
intro;pattern H;apply ind;intros.
  assert (K : Type).
    induction ls.
      exact sg.
      exact sg.
  exact (prod K sg).
Defined.

Lemma k' : a -> Type. (* same lemma but with our bug *)
intro;pattern H;apply ind;intros.
  refine (prod _ _).
    induction ls.
      exact sg.
      exact sg.
    exact sg. (* Proof complete *)
Defined. (* bug *)
