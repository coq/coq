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
(* Bug de 1999 corrig� en d�c 2004 *)

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
Abort.

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

(* The return predicate found should be: "in _=U return U" *)
(* (feature already available in V8.0) *)

Definition g (T1 T2:Type) (x:T1) (e:T1=T2) : T2 :=
  match e with
  | refl_equal => x
  end.

(* An example extracted from FMapAVL which (may) test restriction on
   evars problems of the form ?n[args1]=?n[args2] with distinct args1
   and args2 *)

Set Implicit Arguments.
Parameter t:Set->Set.
Parameter map:forall elt elt' : Set, (elt -> elt') -> t elt -> t elt'.
Parameter avl: forall elt : Set, t elt -> Prop.
Parameter bst: forall elt : Set, t elt -> Prop.
Parameter map_avl: forall (elt elt' : Set) (f : elt -> elt') (m : t elt),
   avl m -> avl (map f m).
Parameter map_bst: forall (elt elt' : Set) (f : elt -> elt') (m : t elt),
   bst m -> bst (map f m).
Record bbst (elt:Set) : Set := 
  Bbst {this :> t elt; is_bst : bst this; is_avl: avl this}.
Definition t' := bbst.
Section B.
Variables elt elt': Set.
Definition map' f (m:t' elt) : t' elt' := 
  Bbst (map_bst f m.(is_bst)) (map_avl f m.(is_avl)).
End B.
Unset Implicit Arguments.

(* An example from Lexicographic_Exponentiation that tests the 
   contraction of reducible fixpoints in type inference *)

Require Import List.
Check (fun (A:Set) (a b x:A) (l:list A) 
  (H : l ++ cons x nil = cons b (cons a nil)) =>
  app_inj_tail l (cons b nil) _ _ H).

(* An example from NMake (simplified), that uses restriction in solve_refl *)

Parameter h:(nat->nat)->(nat->nat).
Fixpoint G p cont {struct p} :=
  h (fun n => match p with O => cont | S p => G p cont end n).

(* An example from Bordeaux/Cantor that applies evar restriction 
   below  a binder *)

Require Import Relations.
Parameter lex : forall (A B : Set), (forall (a1 a2:A), {a1=a2}+{a1<>a2})
-> relation A -> relation B -> A * B -> A * B -> Prop.
Check 
 forall (A B : Set) eq_A_dec o1 o2, 
 antisymmetric A o1 -> transitive A o1 -> transitive B o2 ->
 transitive _ (lex _ _ eq_A_dec o1 o2).

(* Another example from Julien Forest that tests unification below binders *)

Require Import List.
Set Implicit Arguments.
Parameter
 merge : forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
                         (eqB : forall (b1 b2 : B), {b1=b2}+{b1<>b2})
                        (partial_res l : list (A*B)), option (list (A*B)).
Axiom merge_correct :
   forall (A B : Set) eqA eqB (l1 l2 : list (A*B)),
       (forall a2 b2 c2, In (a2,b2) l2 -> In (a2,c2) l2 -> b2 = c2) ->
       match merge eqA eqB l1 l2 with _ => True end.
Unset Implicit Arguments.

(* An example from Bordeaux/Additions that tests restriction below binders *)

Section Additions_while.

Variable A : Set.
Variables P Q : A -> Prop.
Variable le : A -> A -> Prop.
Hypothesis Q_dec : forall s : A, P s -> {Q s} + {~ Q s}.
Hypothesis le_step : forall s : A, ~ Q s -> P s -> {s' | P s' /\ le s' s}.
Hypothesis le_wf : well_founded le.

Lemma loopexec : forall s : A, P s -> {s' : A | P s' /\ Q s'}.
refine
  (well_founded_induction_type le_wf (fun s => _ -> {s' : A | _ /\ _})
    (fun s hr i =>
       match Q_dec s i with
       | left _ => _
       | right _ =>
           match le_step s _ _ with
           | exist s' h' =>
               match hr s' _ _ with
               | exist s'' _ => exist _ s'' _
               end
           end
       end)).
Abort.

End Additions_while.
