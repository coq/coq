(* Check the synthesis of predicate from a cast in case of matching of
   the first component (here [list bool]) of a dependent type (here [sigT])
   (Simplification of an example from file parsing2.v of the Coq'Art
    exercises) *)

Require Import List.

Variable parse_rel : list bool -> list bool -> nat -> Prop.

Variables (l0 : list bool)
  (rec :
     forall l' : list bool,
     length l' <= S (length l0) ->
     {l'' : list bool &
     {t : nat | parse_rel l' l'' t /\ length l'' <= length l'}} +
     {(forall (l'' : list bool) (t : nat), ~ parse_rel l' l'' t)}).

Axiom HHH : forall A : Prop, A.

Check
  (match rec l0 (HHH _) with
   | inleft (existT _ (false :: l1) _) => inright _ (HHH _)
   | inleft (existT _ (true :: l1) (exist _ t1 (conj Hp Hl))) =>
       inright _ (HHH _)
   | inleft (existT _ _ _) => inright _ (HHH _)
   | inright Hnp => inright _ (HHH _)
   end
   :{l'' : list bool &
    {t : nat | parse_rel (true :: l0) l'' t /\ length l'' <= S (length l0)}} +
    {(forall (l'' : list bool) (t : nat), ~ parse_rel (true :: l0) l'' t)}).

(* The same but with relative links to l0 and rec *)

Check
  (fun (l0 : list bool)
     (rec : forall l' : list bool,
            length l' <= S (length l0) ->
            {l'' : list bool &
            {t : nat | parse_rel l' l'' t /\ length l'' <= length l'}} +
            {(forall (l'' : list bool) (t : nat), ~ parse_rel l' l'' t)}) =>
   match rec l0 (HHH _) with
   | inleft (existT _ (false :: l1) _) => inright _ (HHH _)
   | inleft (existT _ (true :: l1) (exist _ t1 (conj Hp Hl))) =>
       inright _ (HHH _)
   | inleft (existT _ _ _) => inright _ (HHH _)
   | inright Hnp => inright _ (HHH _)
   end
   :{l'' : list bool &
    {t : nat | parse_rel (true :: l0) l'' t /\ length l'' <= S (length l0)}} +
    {(forall (l'' : list bool) (t : nat), ~ parse_rel (true :: l0) l'' t)}).
