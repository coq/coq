Require Import TestSuite.admit.
(* -*- coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5302 lines to 4649 lines, then from 4660 lines to 355 lines, then from 360 lines to 269 lines, then from 269 lines to 175 lines, then from 144 lines to 119 lines, then from 297 lines to 117 lines, then from 95 lines to 79 lines, then from 82 lines to 68 lines *)

Set Universe Polymorphism.
Generalizable All Variables.
Inductive sigT {A:Type} (P:A -> Type) : Type := existT : forall x:A, P x -> sigT P.
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Definition projT1 {A} {P : A -> Type} (x : sigT P) : A := let (a, _) := x in a.
Definition projT2 {A} {P : A -> Type} (x : sigT P) : P (projT1 x) := let (a, h) return P (projT1 x) := x in h.
Axiom admit : forall {T}, T.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x := match p with idpath => idpath end.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A ; eisretr : Sect equiv_inv f }.
Record Equiv A B := BuildEquiv { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Existing Instance equiv_isequiv.
Global Instance isequiv_inverse `{IsEquiv A B f} : IsEquiv (@equiv_inv _ _ f _) | 10000 := admit.
Definition equiv_path_sigma `(P : A -> Type) (u v : sigT P)
: Equiv {p : projT1 u = projT1 v &  transport _ p (projT2 u) = projT2 v} (u = v) := admit.
Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.
Definition path_universe {A B : Type} (f : A -> B) : (A = B) := admit.
Section AssumeFunext.
  Let equiv_fibration_replacement_eissect {B C f}
  : forall x : {y : B & {x : C & f x = y}},
      existT _ (f (projT1 (projT2 x))) (existT _ (projT1 (projT2 x)) idpath) = x.
    admit.
  Defined.
  Definition equiv_fibration_replacement  {B C} (f:C ->B):
    Equiv C {y:B & {x:C & f x = y}}.
  Proof.
    refine (BuildEquiv
              _ _ _
              (BuildIsEquiv
                 C {y:B & {x:C & f x = y}}
                 (fun c => existT _ (f c) (existT _ c idpath))
                 (fun c => projT1 (projT2 c))
                 equiv_fibration_replacement_eissect)).
  Defined.
  Definition equiv_total_paths (A : Type) (P : A-> Type) (x y : sigT P) :
    Equiv (x = y) { p : projT1 x = projT1 y & transport P p (projT2 x) = (projT2 y) }
    := BuildEquiv _ _ (@equiv_inv _ _ _ (equiv_path_sigma P x y)) _.
  Variable A:Type.
  Definition Fam A:=sigT (fun I:Type  => I->A).
  Definition p2f: (A->Type)-> Fam A := fun Q:(A->Type) => existT _ (sigT Q) (@projT1 _ _).
  Definition f2p: Fam A -> (A->Type) := fun F => let (I, f) := F in (fun a => (hfiber f a)).
  Definition exp {U V:Type}(w:Equiv U V):Equiv (U->A) (V->A).
    exists (fun f:(U->A)=> (fun x => (f (@equiv_inv _ _ w _ x)))).
    admit.
  Defined.
  Goal { h : Fam A -> A -> Type & Sect h p2f }.
  exists f2p.
  intros [I f].
  set (e:=@equiv_total_paths _ _ (@existT Type (fun I0 : Type => I0 -> A) I f)
                             (existT _ {a : A & hfiber f a} (@projT1 _ _))).
  simpl in e.
  cut ( {p : I = {a : A & @hfiber I A f a} &
                                           @transport _ (fun I0 : Type => I0 -> A) _ _ p f = @projT1 _ _}).
  { intro X.
    apply (inverse (@equiv_inv _ _ _ e X)). }
  set (w:=@equiv_fibration_replacement A I f).
  exists (path_universe w).
  assert (forall x, (exp w) f x = projT1 x); [ | admit ].
  intros [a [i p]].
  exact p.
  Qed.
(* Toplevel input, characters 15-19:
Error: In pattern-matching on term "x" the branch for constructor
"existT(*Top.256 Top.258*)" has type
 "forall (I : Type) (f : I -> A),
  existT (fun I0 : Type => I0 -> A) {a : A & hfiber f a} projT1 =
  existT (fun I0 : Type => I0 -> A) I f" which should be
 "forall (x : Type) (H : x -> A),
  p2f (f2p (existT (fun I : Type => I -> A) x H)) =
  existT (fun I : Type => I -> A) x H".
 *)
