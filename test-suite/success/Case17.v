(* Check the synthesis of predicate from a cast in case of matching of
   the first component (here [list bool]) of a dependent type (here [sigS])
   (Simplification of an example from file parsing2.v of the Coq'Art
    exercises) *)

Require Import PolyList.

Variable parse_rel : (list bool) -> (list bool) -> nat -> Prop.

Variables l0:(list bool); rec:(l' : (list bool))
    (le (length l') (S (length l0))) ->
    {l'' : (list bool) &
    {t : nat | (parse_rel l' l'' t) /\ (le (length l'') (length l'))}} +
    {(l'' : (list bool))(t : nat)~ (parse_rel l' l'' t)}.

Axiom HHH : (A:Prop)A.

Check (Cases (rec l0 (HHH ?)) of
      | (inleft (existS (cons false l1) _)) => (inright ? ? (HHH ?))
      | (inleft (existS (cons true l1) (exist t1 (conj Hp Hl)))) =>
         (inright ? ? (HHH ?))
      | (inleft (existS _ _)) => (inright ? ? (HHH ?))
      | (inright Hnp) => (inright ? ? (HHH ?))
      end ::
   {l'' : (list bool) &
   {t : nat | (parse_rel (cons true l0) l'' t) /\ (le (length l'') (S (length l0)))}} +
   {(l'' : (list bool)) (t : nat) ~ (parse_rel (cons true l0) l'' t)}).
 
(* The same but with relative links to l0 and rec *)
 
Check [l0:(list bool);rec:(l' : (list bool))
    (le (length l') (S (length l0))) ->
    {l'' : (list bool) &
    {t : nat | (parse_rel l' l'' t) /\ (le (length l'') (length l'))}} +
    {(l'' : (list bool)) (t : nat) ~ (parse_rel l' l'' t)}]
   (Cases (rec l0 (HHH ?)) of
      | (inleft (existS (cons false l1) _)) => (inright ? ? (HHH ?))
      | (inleft (existS (cons true l1) (exist t1 (conj Hp Hl)))) =>
         (inright ? ? (HHH ?))
      | (inleft (existS _ _)) => (inright ? ? (HHH ?))
      | (inright Hnp) => (inright ? ? (HHH ?))
      end ::
   {l'' : (list bool) &
   {t : nat | (parse_rel (cons true l0) l'' t) /\ (le (length l'') (S (length l0)))}} +
   {(l'' : (list bool)) (t : nat) ~ (parse_rel (cons true l0) l'' t)}).
