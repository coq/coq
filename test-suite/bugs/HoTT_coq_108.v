Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
(* NOTE: This bug is only triggered with -load-vernac-source / in interactive mode. *)
(* File reduced by coq-bug-finder from 139 lines to 124 lines. *)
Set Universe Polymorphism.
Reserved Notation "g 'o' f" (at level 40, left associativity).
Generalizable All Variables.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
: forall x, f x = g x
  := fun x => match h with idpath => idpath end.

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
  admit.
Defined.
Class IsEquiv {A B : Type} (f : A -> B) := {}.
Class Contr_internal (A : Type) := BuildContr {
                                       center : A ;
                                       contr : (forall y : A, center = y)
                                     }.

Arguments center A {_}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.
Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y.

Notation Contr := (IsTrunc minus_two).

Notation IsHSet := (IsTrunc 0).

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.
Global Instance contr_forall `{Funext} `{P : A -> Type} `{forall a, Contr (P a)}
: Contr (forall a, P a) | 100.
admit.
Defined.
Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.
Global Instance trunc_forall `{Funext} `{P : A -> Type} `{forall a, IsTrunc n (P a)}
: IsTrunc n (forall a, P a) | 100.
Proof.
  generalize dependent P.
  induction n as [ | n' IH]; [ | admit ]; simpl; intros P ?.
                                                        exact _.
Defined.
Set Implicit Arguments.

Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;
    identity : forall x, morphism x x;
    compose : forall s d d', morphism d d' -> morphism s d -> morphism s d';
    trunc_morphism : forall s d, IsHSet (morphism s d) }.

Existing Instance trunc_morphism.
Infix "o" := (@compose _ _ _ _) : morphism_scope.
Local Open Scope morphism_scope.

Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d);
    composition_of : forall s d d'
                            (m1 : morphism C s d) (m2: morphism C d d'),
                       morphism_of _ _ (m2 o m1)
                       = (morphism_of _ _ m2) o (morphism_of _ _ m1);
    identity_of : forall x, morphism_of _ _ (@identity _ x)
                            = @identity _ (object_of x) }.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Section path_functor.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Local Notation path_functor'_T F G
    := { HO : object_of F = object_of G
       & transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }
         (only parsing).
  Definition path_functor'_sig (F G : Functor C D) : path_functor'_T F G -> F = G.
  Proof.
    intros [H' H''].
    destruct F, G; simpl in *.
    induction H'. (* while destruct H' works *) destruct H''.
    apply ap11; [ apply ap | ];
    apply center; abstract exact _.
    Set Printing Universes.
    (* Fail Defined.*)
  (* The command has indeed failed with message:
=> Error: path_functor'_sig_subproof already exists. *)
  Defined.
(* Anomaly: Backtrack.backto 55: a state with no vcs_backup. Please report. *)
End path_functor.
