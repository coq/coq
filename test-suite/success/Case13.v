(* Check coercions in patterns *)

Inductive I : Set :=
  | C1 : nat -> I
  | C2 : I -> I.

Coercion C1 : nat >-> I.

(* Coercion at the root of pattern *)
Check (fun x => match x with
                | C2 n => 0
                | O => 0
                | S n => n
                end).

(* Coercion not at the root of pattern *)
Check (fun x => match x with
                | C2 O => 0
                | _ => 0
                end).

(* Unification and coercions inside patterns *)
Check
  (fun x : option nat => match x with
                         | None => 0
                         | Some O => 0
                         | _ => 0
                         end).

(* Coercion up to delta-conversion, and unification *)
Coercion somenat := Some (A:=nat).
Check (fun x => match x with
                | None => 0
                | O => 0
                | S n => n
                end).

(* Coercions with parameters *)
Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n : nat, nat -> listn n -> listn (S n).

Inductive I' : nat -> Set :=
  | C1' : forall n : nat, listn n -> I' n
  | C2' : forall n : nat, I' n -> I' n.

Coercion C1' : listn >-> I'.
Check (fun x : I' 0 => match x with
                       | C2' _ _ => 0
                       | niln => 0
                       | _ => 0
                       end).
Check (fun x : I' 0 => match x with
                       | C2' _ niln => 0
                       | _ => 0
                       end).

(* This one could eventually be solved, the "Fail" is just to ensure *)
(* that it does not fail with an anomaly, as it did at some time *)
Fail Check (fun x : I' 0 => match x return _ x with
                       | C2' _ _ => 0
                       | niln => 0
                       | _ => 0
                       end).

(* Check insertion of coercions around matched subterm *)

Parameter A:Set.
Parameter f:> A -> nat.

Inductive J : Set := D : A -> J.

Check (fun x => match x with
                | D 0 => 0
                | D _ => 1
                end).

(* Check coercions against the type of the term to match *)
(* Used to fail in V8.1beta *)

Inductive C : Set := c : C.
Inductive E : Set := e :> C -> E.
Check fun (x : E) => match x with c => e c end.

(* Check coercions with uniform parameters (cf bug #1168) *)

Inductive C' : bool -> Set := c' : C' true.
Inductive E' (b : bool) : Set := e' :> C' b -> E' b.
Check fun (x : E' true) => match x with c' => e' true c' end.

(* Check use of the no-dependency strategy when a type constraint is
   given (and when the "inversion-and-dependencies-as-evars" strategy
   is not strong enough because of a constructor with a type whose
   pattern structure is not refined enough for it to be captured by
   the inversion predicate) *)

Inductive K : bool -> bool -> Type := F : K true true | G x : K x x.

Check fun z P Q (y:K true z) (H1 H2:P y) (f:forall y, P y -> Q y z) =>
        match y with
        | F  => f y H1
        | G _ => f y H2
        end : Q y z.

(* Check use of the maximal-dependency-in-variable strategy even when
   no explicit type constraint is given (and when the
   "inversion-and-dependencies-as-evars" strategy is not strong enough
   because of a constructor with a type whose pattern structure is not
   refined enough for it to be captured by the inversion predicate) *)

Check fun z P Q (y:K true z) (H1 H2:P y) (f:forall y z, P y -> Q y z) =>
        match y with
        | F  => f y true H1
        | G b => f y b H2
        end.

(* Check use of the maximal-dependency-in-variable strategy for "Var"
   variables *)

Goal forall z P Q (y:K true z) (H1 H2:P y) (f:forall y z, P y -> Q y z), Q y z.
intros z P Q y H1 H2 f.
Show.
refine (match y with
        | F  => f y true H1
        | G b => f y b H2
        end).
Qed.
