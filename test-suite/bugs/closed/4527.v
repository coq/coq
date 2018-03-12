(* -*- mode: coq; coq-prog-args: ("-nois" "-indices-matter" "-R" "." "Top" "-top" "bug_bad_univ_length_01") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1199 lines to 
430 lines, then from 444 lines to 430 lines, then from 964 lines to 255 lines, 
then from 269 lines to 255 lines *)
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

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive True : Type :=
  I : True.
Module Export Datatypes.

Set Implicit Arguments.
Notation nat := Coq.Init.Datatypes.nat.
Notation O := Coq.Init.Datatypes.O.
Notation S := Coq.Init.Datatypes.S.
Notation two := (S (S O)).

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Notation "x * y" := (prod x y) : type_scope.

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

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

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
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B}%type_scope f%function_scope {_} _.
Arguments eissect {A B}%type_scope f%function_scope {_} _.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : 
function_scope.

Inductive Unit : Type1 :=
    tt : Unit.

Local Open Scope path_scope.

Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.

  Theorem other_adj (b : B) : eissect f (f^-1 b) = ap f^-1 (eisretr f b).
admit.
Defined.

  Global Instance isequiv_inverse : IsEquiv f^-1 | 10000
    := BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj.
End EquivInverse.

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

  Parameter inO_equiv_inO@{u a i j k} :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),

        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U.

  Parameter extendable_to_O@{u a i j k}
  : forall (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : 
Type2le@{j a}} {Q_inO : In@{u a j} O Q},
      ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).

End ReflectiveSubuniverses.

Module ReflectiveSubuniverses_Theory (Os : ReflectiveSubuniverses).
Export Os.

Existing Class In.

  Coercion O_reflector : ReflectiveSubuniverse >-> Funclass.

Arguments inO_equiv_inO {O} T {U} {_} f {_}.
Global Existing Instance O_inO.

Section ORecursion.
  Context {O : ReflectiveSubuniverse}.

  Definition O_indpaths {P Q : Type} {Q_inO : In O Q}
             (g h : O P -> Q) (p : g o to O P == h o to O P)
  : g == h
  := (fst (snd (extendable_to_O O two) g h) p).1.

  Definition O_indpaths_beta {P Q : Type} {Q_inO : In O Q}
             (g h : O P -> Q) (p : g o (to O P) == h o (to O P)) (x : P)
  : O_indpaths g h p (to O P x) = p x
  := (fst (snd (extendable_to_O O two) g h) p).2 x.

End ORecursion.

Section Reflective_Subuniverse.
  Universes Ou Oa.
  Context (O : ReflectiveSubuniverse@{Ou Oa}).

    Definition inO_isequiv_to_O (T:Type)
    : IsEquiv (to O T) -> In O T
    := fun _ => inO_equiv_inO (O T) (to O T)^-1.

    Definition inO_to_O_retract (T:Type) (mu : O T -> T)
    : Sect (to O T) mu -> In O T.
    Proof.
      unfold Sect; intros H.
      apply inO_isequiv_to_O.
      apply isequiv_adjointify with (g:=mu).
      -
 refine (O_indpaths (to O T o mu) idmap _).
        intros x; exact (ap (to O T) (H x)).
      -
 exact H.
    Defined.

    Definition inO_paths@{i} (S : Type@{i}) {S_inO : In@{Ou Oa i} O S} (x y : 
S)    : In@{Ou Oa i} O (x=y).
    Proof.
      simple refine (inO_to_O_retract@{i} _ _ _); intro u.
      -
 assert (p : (fun _ : O (x=y) => x) == (fun _=> y)).
        {
 refine (O_indpaths _ _ _); simpl.
          intro v; exact v.
}
        exact (p u).
      -
 hnf.
        rewrite O_indpaths_beta; reflexivity.
    Qed.
    Check inO_paths@{Type}.
