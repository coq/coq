(* The "?" of cons and eq should be inferred *)
Variable list : Set -> Set.
Variable cons : forall T : Set, T -> list T -> list T.
Check (forall n : list nat, exists l : _, (exists x : _, n = cons _ x l)).

(* Examples provided by Eduardo Gimenez *)

Definition c A (Q : (nat * A -> Prop) -> Prop) P :=
  Q (fun p : nat * A => let (i, v) := p in P i v).

(* What does this test ? *)
Require Import List.
Definition list_forall_bool (A : Set) (p : A -> bool) 
  (l : list A) : bool :=
  fold_right (fun a r => if p a then r else false) true l.

(* Checks that solvable ? in the lambda prefix of the definition are harmless*)
Parameter A1 A2 F B C : Set.
Parameter f : F -> A1 -> B.
Definition f1 frm0 a1 : B := f frm0 a1.

(* Checks that solvable ? in the type part of the definition are harmless *)
Definition f2 frm0 a1 : B := f frm0 a1.

(* Checks that sorts that are evars are handled correctly (bug 705) *)
Require Import List.

Fixpoint build (nl : list nat) :
 match nl with
 | nil => True
 | _ => False
 end -> unit :=
  match nl return (match nl with
                   | nil => True
                   | _ => False
                   end -> unit) with
  | nil => fun _ => tt
  | n :: rest =>
      match n with
      | O => fun _ => tt
      | S m => fun a => build rest (False_ind _ a)
      end
  end.


(* Checks that disjoint contexts are correctly set by restrict_hyp *)
(* Bug de 1999 corrigé en déc 2004 *)

Check
  (let p :=
     fun (m : nat) f (n : nat) =>
     match f m n with
     | exist a b => exist _ a b
     end in
   p
   :forall x : nat,
    (forall y n : nat, {q : nat | y = q * n}) ->
    forall n : nat, {q : nat | x = q * n}).

(* Check instantiation of nested evars (bug #1089) *)

Check (fun f:(forall (v:Type->Type), v (v nat) -> nat) => f _ (Some (Some O))).

(* This used to fail with anomaly "evar was not declared" in V8.0pl3 *)

Theorem contradiction : forall p, ~ p -> p -> False.
Proof. trivial. Qed.
Hint Resolve contradiction.
Goal False.
eauto.

(* This used to fail in V8.1beta because first-order unification was
   used before using type information *)

Check (exist _ O (refl_equal 0) : {n:nat|n=0}).
Check (exist _ O I : {n:nat|True}).

(* An example (initially from Marseille/Fairisle) that involves an evar with
   different solutions (Input, Output or bool) that may or may not be
   considered distinct depending on which kind of conversion is used *)

Section A.
Definition STATE := (nat * bool)%type.
Let Input := bool.
Let Output := bool.
Parameter Out : STATE -> Output.
Check fun (s : STATE) (reg : Input) => reg = Out s.
End A.
