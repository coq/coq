Module Test0.

(* By default all coercions from a Structure/Record are also reversible, unless:

     Structure foo := {
      ..
      #[reversible=no] bla :> blu
     }

   is given
*)

(* Declaring/undeclaring a reverse coercion after the facts:

    #[reversible] Coercion sort.
    #[reversible=yes] Coercion sort.

    #[reversible=no] Coercion sort.
*)

Structure S := {
  ssort :> Type;
  sstuff : ssort;
}.

Definition test1 (s : S) (x : s) := sstuff s.
Definition test2 (s : S) := sstuff s.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.
Set Printing All.
Check test1 _ (0 : nat).

(* old hack *)
Definition test' {s : S} (t : Type) (f : ssort s -> t) := sstuff s.
Notation test t := (test' t (fun x => x)).
Check test nat.

(* new *)
Check test2 (nat : Type).
Definition nat' (x:unit) := nat.
Arguments nat' &.
(* checks that reapply_coercions gets the right trace *)
Check test2 (nat' tt).
Check (nat : S).

Structure R := {
  rsort :> Type;
  rstuff : rsort;
  srstuff : rsort;
}.

Coercion RtoS (r : R) := {| ssort := rsort r ; sstuff := srstuff r|}.
Canonical RtoS.

Canonical Structure R_nat := {| rsort := nat; rstuff := 1; srstuff := 0 |}.

Definition test3 (r : R) := rstuff r.

Set Printing All.
Check test3 nat.
Check test3 S_nat.

Structure T := {
  tsort :> Type;
}.

Canonical T_nat (x : unit) := {| tsort := nat |}.

Check test2 (T_nat tt).



Structure A := { }.
Structure A' := { }.
Structure B := { ba :> A; #[canonical=no] ba' :> A' }.
Structure C := { ca :> A; #[canonical=no] ca' :> A' }.
Axiom f : A -> A'.
Coercion f : A >-> A'.

Canonical b : B := {| ba := Build_A; ba' := Build_A' |}.
Canonical c : C := {| ca := Build_A; ca' := Build_A' |}.

Definition test4 (x : B) := 1.
Check test4 c.






(* ~~> test S_nat : S_nat.sort
                             Type ==?== S
                               :
                             f : nat ---> S_nat

                              sort : S >-> Type

                             f :=
                              nat ----> ?x
                              sort ?x ==?== nat
                            *)

End Test0.

(* Test the reverse attribute *)
Module Test1.

Structure S := {
  ssort : Type;
  sstuff : ssort;
}.

#[reversible=no] Coercion ssort : S >-> Sortclass.

Definition test2 (s : S) := sstuff s.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.
Fail Check test2 (nat : Type).

End Test1.

(* Test the reverse attribute *)
Module Test1'.

Structure S := {
  ssort : Type;
  sstuff : ssort;
}.

Coercion ssort : S >-> Sortclass.

Definition test2 (s : S) := sstuff s.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.
Fail Check test2 (nat : Type).

End Test1'.

(* Test the reverse attribute *)
Module Test2.

Structure S := {
  #[reversible=no] ssort :> Type;
  sstuff : ssort;
}.

Definition test2 (s : S) := sstuff s.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.
Fail Check test2 (nat : Type).

End Test2.

(* Test the reverse attribute *)
Module Test3.

Structure S := {
  #[reversible=no] ssort :> Type;
  sstuff : ssort;
}.

Definition test2 (s : S) := sstuff s.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.

#[reversible] Coercion ssort.

Check test2 (nat : Type).

End Test3.

(* Test the reverse attribute *)
Module Test4.

Structure S := {
  ssort :> Type;
  sstuff : ssort;
}.

Definition test2 (s : S) := sstuff s.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.

#[reversible=no] Coercion ssort.

Fail Check test2 (nat : Type).

End Test4.
