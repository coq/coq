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
