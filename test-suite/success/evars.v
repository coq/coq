
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

(* Checks that sorts that are evars are handled correctly (BZ#705) *)
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
     | exist _ a b => exist _ a b
     end in
   p
   :forall x : nat,
    (forall y n : nat, {q : nat | y = q * n}) ->
    forall n : nat, {q : nat | x = q * n}).

(* Check instantiation of nested evars (BZ#1089) *)

Check (fun f:(forall (v:Type->Type), v (v nat) -> nat) => f _ (Some (Some O))).

(* This used to fail with anomaly (Pp.str "evar was not declared.") in V8.0pl3 *)

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
           | exist _ s' h' =>
               match hr s' _ _ with
               | exist _ s'' _ => exist _ s'' _
               end
           end
       end)).
Abort.

End Additions_while.

(* Two examples from G. Melquiond (BZ#1878 and BZ#1884) *)

Parameter F1 G1 : nat -> Prop.
Goal forall x : nat, F1 x -> G1 x.
refine (fun x H => proj2 (_ x H)).
Abort.

Goal forall x : nat, F1 x -> G1 x.
refine (fun x H => proj2 (_ x H) _).
Abort.

(* An example from y-not that was failing in 8.2rc1 *)

Fixpoint filter (A:nat->Set) (l:list (sigT A)) : list (sigT A) :=
  match l with
  | nil => nil
  | (existT _ k v)::l' => (existT _ k v):: (filter A l')
  end.

(* BZ#2000: used to raise Out of memory in 8.2 while it should fail by
   lack of information on the conclusion of the type of j *)

Goal True.
set (p:=fun j => j (or_intror _ (fun a:True => j (or_introl _ a)))) || idtac.
Abort.

(* Remark: the following example stopped succeeding at some time in
   the development of 8.2 but it works again (this was because 8.2
   algorithm was more general and did not exclude a solution that it
   should have excluded for typing reason; handling of types and
   backtracking is still to be done) *)

Section S.
Variables A B : nat -> Prop.
Goal forall x : nat, A x -> B x.
refine (fun x H => proj2 (_ x H) _).
Abort.
End S.

(* Check that constraints are taken into account by tactics that instantiate *)

Lemma inj : forall n m, S n = S m -> n = m.
intros n m H.
eapply f_equal with (* should fail because ill-typed *)
  (f := fun n =>
        match n return match n with S _ => nat | _ => unit end with
        | S n => n
        | _ => tt
        end) in H
|| injection H.
Abort.

(* A legitimate simple eapply that was failing in coq <= 8.3.
   Cf. in Unification.w_merge the addition of an extra pose_all_metas_as_evars
   on 30/9/2010
*)

Lemma simple_eapply_was_failing :
 (forall f:nat->nat, exists g, f = g) -> True.
Proof.
 assert (modusponens : forall P Q, P -> (P->Q) -> Q) by auto.
 intros.
 eapply modusponens.
 simple eapply H.
 (* error message with V8.3 :
    Impossible to unify "?18" with "fun g : nat -> nat => ?6 = g". *)
Abort.

(* Regression test *)

Definition fo : option nat -> nat := option_rec _ (fun a => 0) 0.

(* This example revealed an incorrect evar restriction at some time
   around October 2011 *)

Goal forall (A:Type) (a:A) (P:forall A, A -> Prop), (P A a) /\ (P A a).
intros.
refine ((fun H => conj (proj1 H) (proj2 H)) _).
Abort.

(* The argument of e below failed to be inferred from r14219 (Oct 2011) to *)
(* r14753 after the restrictions made on detecting Miller's pattern in the *)
(* presence of alias, only the second-order unification procedure was *)
(* able to solve this problem but it was deactivated for 8.4 in r14219 *)

Definition k0
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, exists n : nat, n = a) o :=
 match o with (* note: match introduces an alias! *)
 | Some a => e _ (j a)
 | None => O
 end.

Definition k1
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, exists n : nat, n = a) a (b:=a) := e _ (j a).

Definition k2
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, exists n : nat, n = a) a (b:=a) := e _ (j b).

(* Other examples about aliases involved in pattern unification *)

Definition k3
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, exists n : nat, let a' := a in n = a') a (b:=a) := e _ (j b).

Definition k4
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, exists n : nat, let a' := S a in n = a') a (b:=a) := e _ (j b).

Definition k5
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, let a' := S a in exists n : nat, n = a') a (b:=a) := e _ (j b).

Definition k6
  (e:forall P : nat -> Prop, (exists n : nat, P n) -> nat)
  (j : forall a, exists n : nat, let n' := S n in n' = a) a (b:=a) := e _ (j b).

Definition k7
  (e:forall P : nat -> Prop, (exists n : nat, let n' := n in P n') -> nat)
  (j : forall a, exists n : nat, n = a) a (b:=a) := e _ (j b).

(* An example that uses materialize_evar under binders *)
(* Extracted from bigop.v in the mathematical components library *)

Section Bigop.

Variable bigop : forall R I: Type,
  R -> (R -> R -> R) -> list I -> (I->Prop) -> (I -> R) -> R.

Hypothesis eq_bigr :
forall (R : Type) (idx : R) (op : R -> R -> R)
       (I : Type) (r : list I) (P : I -> Prop) (F1 F2 : I -> R),
       (forall i : I, P i -> F1 i = F2 i) ->
       bigop R I idx op r (fun i : I => P i) (fun i : I => F1 i) = idx.

Hypothesis big_tnth :
forall (R : Type) (idx : R) (op : R -> R -> R)
     (I : Type) (r : list I) (P : I -> Prop) (F : I -> R),
     bigop R I idx op r (fun i : I => P i) (fun i : I => F i) = idx.

Hypothesis big_tnth_with_letin :
forall (R : Type) (idx : R) (op : R -> R -> R)
     (I : Type) (r : list I) (P : I -> Prop) (F : I -> R),
     bigop R I idx op r (fun i : I => let i:=i in P i) (fun i : I => F i) = idx.

Variable R : Type.
Variable idx : R.
Variable op : R -> R -> R.
Variable I : Type.
Variable J : Type.
Variable rI : list I.
Variable rJ : list J.
Variable xQ : J -> Prop.
Variable P : I -> Prop.
Variable Q : I -> J -> Prop.
Variable F : I -> J -> R.

(* Check unification under binders *)

Check (eq_bigr _ _ _ _ _ _ _ _ (fun _ _ => big_tnth _ _ _ _ rI _ _))
  : (bigop R J idx op rJ
        (fun j : J => let k:=j in xQ k)
        (fun j : J => let k:=j in 
         bigop R I idx
           op rI
           (fun i : I => P i /\ Q i k) (fun i : I => let k:=j in F i k))) = idx.

(* Check also with let-in *)

Check (eq_bigr _ _ _ _ _ _ _ _ (fun _ _ => big_tnth_with_letin _ _ _ _ rI _ _))
  : (bigop R J idx op rJ
        (fun j : J => let k:=j in xQ k)
        (fun j : J => let k:=j in 
         bigop R I idx
           op rI
           (fun i : I => P i /\ Q i k) (fun i : I => let k:=j in F i k))) = idx.

End Bigop.

(* Check the use of (at least) an heuristic to solve problems of the form
   "?x[t] = ?y" where ?y occurs in t without easily knowing if ?y can
   eventually be erased in t *)

Section evar_evar_occur.
  Variable id : nat -> nat.
  Variable f : forall x, id x = 0 -> id x = 0 -> x = 1 /\ x = 2.
  Variable g : forall y, id y = 0 /\ id y = 0.
  (* Still evars in the resulting type, but constraints should be solved *)
  Check match g _ with conj a b => f _ a b end.
End evar_evar_occur.

(* Eta expansion (BZ#2936) *)
Record iffT (X Y:Type) : Type := mkIff { iffLR : X->Y; iffRL : Y->X }.
Record tri (R:Type->Type->Type) (S:Type->Type->Type) (T:Type->Type->Type) := mkTri {
  tri0 : forall a b c, R a b -> S a c -> T b c
}.
Arguments mkTri [R S T].
Definition tri_iffT : tri iffT iffT iffT :=
  (mkTri
    (fun X0 X1 X2 E01 E02 =>
     (mkIff _ _ (fun x1 => iffLR _ _ E02 (iffRL _ _ E01 x1))
     (fun x2 => iffLR _ _ E01 (iffRL _ _ E02 x2))))).

(* Check that local defs names are preserved if possible during unification *)

Goal forall x (x':=x) (f:forall y, y=y:>nat -> Prop), f _ (eq_refl x').
intros.
unfold x' at 2. (* A way to check that there are indeed 2 occurrences of x' *)
Abort.

(* A simple example we would like not to fail (it used to fail because of
   not strict enough evar restriction) *)

Check match Some _ with None => _ | _ => _ end.

(* Used to fail for a couple of days in Nov 2014 *)

Axiom test : forall P1 P2, P1 = P2 -> P1 -> P2.

(* Check use of candidates *)

Import EqNotations.
Definition test2 {A B:Type} {H:A=B} (a:A) : B := rew H in a.

(* Check that pre-existing evars are not counted as newly undefined in "set" *)
(* Reported by Théo *)

Goal exists n : nat, n = n -> True.
eexists.
set (H := _ = _).
Abort.

(* Check interpretation of default evar instance in pretyping *)
(* (reported as bug #7356) *)

Check fun (P : nat -> Prop) (x:nat) (h:P x) => exist _ ?[z] (h : P ?z).
