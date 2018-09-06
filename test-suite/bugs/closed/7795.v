

Definition fwd (b: bool) A (e2: A): A. Admitted.

Ltac destruct_refinement_aux T :=
  let m := fresh "mres" in
  let r := fresh "r" in
  let P := fresh "P" in
  pose T as m;
  destruct m as [ r P ].

Ltac destruct_refinement :=
  match goal with
  | |- context[proj1_sig ?T] => destruct_refinement_aux T
  end.

Ltac t_base := discriminate || destruct_refinement.


Inductive List (T: Type) :=
| Cons_construct: T -> List T -> List T
| Nil_construct: List T.

Definition t (T: Type): List T. Admitted.
Definition size (T: Type) (src: List T): nat. Admitted.
Definition filter1_rt1_type (T: Type): Type := { res: List T | false = true }.
Definition filter1 (T: Type): filter1_rt1_type T. Admitted.

Definition hh_1:
  forall T : Type,
    (forall (T0 : Type),
     False -> filter1_rt1_type T0) ->
     False.
Admitted.

Definition hh_2:
  forall (T : Type),
    filter1_rt1_type T ->
    filter1_rt1_type T.
Admitted.

Definition hh:
  forall (T : Type) (f1 : forall (T0 : Type), False -> filter1_rt1_type T0),
       fwd
         (Nat.leb
               (size T
                  (fwd false (List T)
                     (fwd false (List T)
                        (proj1_sig
                           (hh_2 T
                              (f1 T (hh_1 T f1))))))) 0) bool
         false = true.
Admitted.

Set Program Mode. (* removing this line prevents the bug *)
Obligation Tactic := repeat t_base.

Goal
  forall T (h17: T),
    filter1 T =
    exist
      _
      (Nil_construct T)
      (hh T (fun (T : Type) (_ : False) => filter1 T)).
Abort.
