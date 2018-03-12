(* -*- mode: coq; coq-prog-args: ("-nois" "-indices-matter" "-R" "." "Top" "-top" "bug_lex_wrong_rewrite_02") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1125 lines to 
346 lines, then from 360 lines to 346 lines, then from 822 lines to 271 lines, 
then from 285 lines to 271 lines *)
(* coqc version 8.5 (January 2016) compiled on Jan 23 2016 16:15:22 with OCaml 
4.01.0
   coqtop version 8.5 (January 2016) *)
Declare ML Module "ltac_plugin".
Inductive False := .
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Global Set Universe Polymorphism.
Global Set Primitive Projections.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Module Export Datatypes.
  Set Implicit Arguments.
  Notation nat := Coq.Init.Datatypes.nat.
  Notation O := Coq.Init.Datatypes.O.
  Notation S := Coq.Init.Datatypes.S.
  Notation one := (S O).
  Notation two := (S one).
  Record prod (A B : Type) := pair { fst : A ; snd : B }.
  Notation "x * y" := (prod x y) : type_scope.
  Delimit Scope nat_scope with nat.
  Open Scope nat_scope.
End Datatypes.
Module Export Specif.
  Set Implicit Arguments.
  Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P 
proj1_sig }.
  Notation sigT := sig (only parsing).
  Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
  Notation projT1 := proj1_sig (only parsing).
  Notation projT2 := proj2_sig (only parsing).
End Specif.
Global Set Keyed Unification.
Global Unset Strict Universe Declaration.
Definition Type1@{i} := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.
Definition Type2@{i j} := Eval hnf in let gt := (Type1@{j} : Type@{i}) in 
Type@{i}.
Definition Type2le@{i j} := Eval hnf in let gt := (Set : Type@{i}) in
                                        let ge := ((fun x => x) : Type1@{j} -> 
Type@{i}) in Type@{i}.
Notation idmap := (fun x => x).
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Open Scope fibration_scope.
Open Scope function_scope.
Notation pr1 := projT1.
Notation pr2 := projT2.
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.
Notation compose := (fun g f x => g (f x)).
Notation "g 'o' f" := (compose g%function f%function) (at level 40, left 
associativity) : function_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.
Notation "1" := idpath : path_scope.
Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.
Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : 
type_scope.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
                                               equiv_inv : B -> A ;
                                               eisretr : Sect equiv_inv f;
                                               eissect : Sect f equiv_inv;
                                               eisadj : forall x : A, eisretr 
(f x) = ap f (eissect x)
                                             }.
Arguments eissect {A B}%type_scope f%function_scope {_} _.
Inductive Unit : Type1 := tt : Unit.
Local Open Scope path_scope.
Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z 
= t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with idpath =>
               match q with idpath =>
                            match p with idpath => 1
                            end end end.
Section Adjointify.
  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).
  Let issect' := fun x =>
                   ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
    admit.
  Defined.

  Definition isequiv_adjointify : IsEquiv f
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.
End Adjointify.
Definition ExtensionAlong {A B : Type} (f : A -> B)
           (P : B -> Type) (d : forall x:A, P (f x))
  := { s : forall y:B, P y & forall x:A, s (f x) = d x }.
Fixpoint ExtendableAlong@{i j k l}
         (n : nat) {A : Type@{i}} {B : Type@{j}}
         (f : A -> B) (C : B -> Type@{k}) : Type@{l}
  := match n with
     | O => Unit@{l}
     | S n => (forall (g : forall a, C (f a)),
                  ExtensionAlong@{i j k l l} f C g) *
              forall (h k : forall b, C b),
                ExtendableAlong n f (fun b => h b = k b)
     end.

Definition ooExtendableAlong@{i j k l}
           {A : Type@{i}} {B : Type@{j}}
           (f : A -> B) (C : B -> Type@{k}) : Type@{l}
  := forall n, ExtendableAlong@{i j k l} n f C.

Module Type ReflectiveSubuniverses.

  Parameter ReflectiveSubuniverse@{u a} : Type2@{u a}.

  Parameter O_reflector@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
      Type2le@{i a} -> Type2le@{i a}.

  Parameter In@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
      Type2le@{i a} -> Type2le@{i a}.

  Parameter O_inO@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : 
Type@{i}),
      In@{u a i} O (O_reflector@{u a i} O T).

  Parameter to@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : 
Type@{i}),
      T -> O_reflector@{u a i} O T.

  Parameter extendable_to_O@{u a i j k}
    : forall (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : 
Type2le@{j a}} {Q_inO : In@{u a j} O Q},
      ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).

End ReflectiveSubuniverses.

Module ReflectiveSubuniverses_Theory (Os : ReflectiveSubuniverses).
  Export Os.
  Existing Class In.
  Module Export Coercions.
    Coercion O_reflector : ReflectiveSubuniverse >-> Funclass.
  End Coercions.
  Global Existing Instance O_inO.

  Section ORecursion.
    Context {O : ReflectiveSubuniverse}.

    Definition O_rec {P Q : Type} {Q_inO : In O Q}
               (f : P -> Q)
      : O P -> Q
      := (fst (extendable_to_O O one) f).1.

    Definition O_rec_beta {P Q : Type} {Q_inO : In O Q}
               (f : P -> Q) (x : P)
      : O_rec f (to O P x) = f x
      := (fst (extendable_to_O O one) f).2 x.

    Definition O_indpaths {P Q : Type} {Q_inO : In O Q}
               (g h : O P -> Q) (p : g o to O P == h o to O P)
      : g == h
      := (fst (snd (extendable_to_O O two) g h) p).1.

  End ORecursion.


  Section Reflective_Subuniverse.
    Context (O : ReflectiveSubuniverse@{Ou Oa}).

    Definition isequiv_to_O_inO@{u a i} (T : Type@{i}) `{In@{u a i} O T} : 
IsEquiv@{i i} (to O T).
    Proof.

      pose (g := O_rec@{u a i i i i i} idmap).
      refine (isequiv_adjointify (to O T) g _ _).
      -
        refine (O_indpaths@{u a i i i i i} (to O T o g) idmap _).
        intros x.
        apply ap.
        apply O_rec_beta.
      -
        intros x.
        apply O_rec_beta.
    Defined.
    Global Existing Instance isequiv_to_O_inO.

  End Reflective_Subuniverse.

End ReflectiveSubuniverses_Theory.

Module Type Preserves_Fibers (Os : ReflectiveSubuniverses).
  Module Export Os_Theory := ReflectiveSubuniverses_Theory Os.
End Preserves_Fibers.

Opaque eissect.
Module Lex_Reflective_Subuniverses
       (Os : ReflectiveSubuniverses) (Opf : Preserves_Fibers Os).
  Import Opf.
  Goal forall (O : ReflectiveSubuniverse) (A : Type) (B : A -> Type) (A_inO : 
In O A),

      forall g,
      forall (x : O {x : A & B x}) v v' v'' (p2 : v'' = v') (p0 : v' = v) (p1 : 
v = _) r,
        (p2
           @ (p0
                @ p1))
          @ eissect (to O A) (g x) = r.
    intros.
    cbv zeta.
    rewrite concat_p_pp.
    match goal with
    | [ |- p2 @ p0 @ p1 @ eissect (to O A) (g x) = r ] => idtac "good"
    | [ |- ?G ] => fail 1 "bad" G
    end.
    Fail rewrite concat_p_pp.
