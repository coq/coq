
Require Import Equality.

Parameter Patch : nat -> nat -> Set.

Inductive Catch (from to : nat) : Type
    := MkCatch : forall (p : Patch from to),
                 Catch from to.
Arguments MkCatch [from to].

Inductive CatchCommute5
        : forall {from mid1 mid2 to : nat},
          Catch from mid1
       -> Catch mid1 to
       -> Catch from mid2
       -> Catch mid2 to
       -> Prop
     := MkCatchCommute5 :
           forall {from mid1 mid2 to : nat}
                  (p : Patch from mid1)
                  (q : Patch mid1 to)
                  (q' : Patch from mid2)
                  (p' : Patch mid2 to),
           CatchCommute5 (MkCatch p) (MkCatch q) (MkCatch q') (MkCatch p').

Inductive CatchCommute {from mid1 mid2 to : nat}
                       (p : Catch from mid1)
                       (q : Catch mid1 to)
                       (q' : Catch from mid2)
                       (p' : Catch mid2 to)
                     : Prop
    := isCatchCommute5 : forall (catchCommuteDetails : CatchCommute5 p q q' p'),
                         CatchCommute p q q' p'.
Notation "<< p , q >> <~> << q' , p' >>"
    := (CatchCommute p q q' p')
    (at level 60, no associativity).

Lemma CatchCommuteUnique2 :
      forall {from mid mid' to : nat}
             {p   : Catch from mid}  {q   : Catch mid  to}
             {q'  : Catch from mid'} {p'  : Catch mid' to}
             {q'' : Catch from mid'} {p'' : Catch mid' to}
             (commute1 : <<p, q>> <~> <<q', p'>>)
             (commute2 : <<p, q>> <~> <<q'', p''>>),
      (p' = p'') /\ (q' = q'').
Proof with auto.
intros.
set (X := commute2).
Fail dependent destruction commute1;
dependent destruction catchCommuteDetails;
dependent destruction commute2;
dependent destruction catchCommuteDetails generalizing X.
revert X.
dependent destruction commute1;
dependent destruction catchCommuteDetails;
dependent destruction commute2;
dependent destruction catchCommuteDetails.
Abort.
