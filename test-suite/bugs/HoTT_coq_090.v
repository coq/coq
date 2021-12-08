Require Import TestSuite.admit.
(** I'm not sure if this tests what I want it to test... *)
Set Implicit Arguments.
Set Universe Polymorphism.

Notation idmap := (fun x => x).

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.
Arguments paths_rect [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments concat {A x y z} p q : simpl nomatch.

(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

(** Declaring this as [simpl nomatch] prevents the tactic [simpl] from expanding it out into [match] statements.  We only want [inverse] to simplify when applied to an identity path. *)
Arguments inverse {A x y} p : simpl nomatch.

(** Note that you can use the built-in Coq tactics [reflexivity] and [transitivity] when working with paths, but not [symmetry], because it is too smart for its own good.  Instead, you can write [apply symmetry] or [eapply symmetry]. *)

(** The identity path. *)
Notation "1" := idpath : path_scope.

(** The composition of two paths. *)
Notation "p @ q" := (concat p q) (at level 20) : path_scope.

(** The inverse of a path. *)
Notation "p ^" := (inverse p) (at level 3) : path_scope.

(** An alternative notation which puts each path on its own line.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'") : long_path_scope.


(** An important instance of [paths_rect] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments transport {A} P {x y} p%path_scope u : simpl nomatch.



Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p) | 0.
Proof.
  unshelve refine (@BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^) _ _ _);
  admit.
Defined.

Definition equiv_path (A B : Type) (p : A = B) : Equiv A B
  := @BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Arguments equiv_path : clear implicits.

Definition equiv_adjointify A B (f : A -> B) (g : B -> A) (r : Sect g f) (s : Sect f g) : Equiv A B.
Proof.
  refine (@BuildEquiv A B f (@BuildIsEquiv A B f g r s _)).
  admit.
Defined.


Set Printing Universes.

Definition lift_id_type : Type.
Proof.
  let U0 := constr:(Type) in
  let U1 := constr:(Type) in
  let unif := constr:(U0 : U1) in
  exact (forall (A : Type) (B : Type), @paths U0 A B -> @paths U1 A B).
Defined.

Definition lower_id_type : Type.
Proof.
  let U0 := constr:(Type) in
  let U1 := constr:(Type) in
  let unif := constr:(U0 : U1) in
  exact ((forall (A : Type) (B : Type), IsEquiv (equiv_path (A : U0) (B : U0)))
         -> forall (A : Type) (B : Type),  @paths U1 A B -> @paths U0 A B).
Defined.

Definition lift_id : lift_id_type :=
  fun A B p => match p in @paths _ _ B return @paths Type (A : Type) (B : Type) with
                 | idpath => idpath
               end.

Definition lower_id : lower_id_type.
Proof.
  intros ua A B p.
  specialize (ua A B).
  apply (@equiv_inv _ _ (equiv_path A B) _).
  simpl.
  pose (f := transport idmap p : A -> B).
  pose (g := transport idmap p^ : B -> A).
  refine (@equiv_adjointify
            _ _
            f g
            _ _);
    subst f g; unfold transport, inverse;
    clear ua;
    [ intro x
    | exact match p as p in (_ = B) return
                  (forall x : (A : Type),
                     @paths (* Top.904 *)
                       A
                       match
                         match
                           p in (paths _ a)
                           return (@paths (* Top.906 *) Type (* Top.900 *) a A)
                         with
                           | idpath => @idpath (* Top.906 *) Type (* Top.900 *) A
                         end in (paths _ a) return a
                       with
                         | idpath => match p in (paths _ a) return a with
                                       | idpath => x
                                     end
                       end x)
            with
              | idpath => fun _ => idpath
            end ].

  - pose proof (match p as p in (_ = B) return
                      (forall x : (B : Type),
                         match p in (_ = a) return (a : Type) with
                           | idpath =>
                             match
                               match p in (_ = a) return (@paths Type (a : Type) (A : Type)) with
                                 | idpath => idpath
                               end in (_ = a) return (a : Type)
                             with
                               | idpath => x
                             end
                         end = x)
                with
                  | idpath => fun _ => idpath
                end x) as p'.
    admit.
Defined.
(* Error: Illegal application:
The term "paths (* Top.96 *)" of type
 "forall A : Type (* Top.96 *), A -> A -> Type (* Top.96 *)"
cannot be applied to the terms
 "Type (* Top.100 *)" : "Type (* Top.100+1 *)"
 "a" : "Type (* Top.60 *)"
 "A" : "Type (* Top.57 *)"
The 2nd term has type "Type (* Top.60 *)" which should be coercible to
 "Type (* Top.100 *)".
 *)
