(* Test that it raises a normal error and not an anomaly *)
Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.
Arguments fst {A B} _.
Arguments snd {A B} _.
Arguments pair {A B} _ _.
Record piis := { dep_types : Type; indep_args : dep_types -> Type }.
Import EqNotations.
Goal forall (id : Set) (V : id) (piiio : id -> piis)
            (Z : {ridc : id & prod (dep_types (piiio ridc)) True})
            (P : dep_types (piiio V) -> Type) (W : {x : dep_types (piiio V) & P x}),
    let ida := fun (x : id) (y : dep_types (piiio x)) => indep_args (piiio x) y in
    prod True (ida V (projT1 W)) ->
    Z = existT _ V (pair (projT1 W) I) ->
    ida (projT1 Z) (fst (projT2 Z)).
  intros.
  refine  (rew <- [fun k' => ida (projT1 k') (fst (projT2 k'))]
               H in
              let v := I in
              _);
    refine (snd X).
  Undo.
Fail refine (rew <- [fun k' => ida (projT1 k') (fst (projT2 k'))]
              H in
             let v := I in
             snd X).
Abort.
