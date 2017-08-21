Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Notation "x = y" := (@paths _ x y) : type_scope.
Definition concat {A} {x y z : A} : x = y -> y = z -> x = z. Admitted.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x. Admitted.
Notation "p @ q" := (concat p q) (at level 20).
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y. Admitted.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y. Admitted.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : forall x, f (equiv_inv x) = x;
  eissect : forall x, equiv_inv (f x) = x
}.

Class Contr_internal (A : Type).

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.
Definition istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y).
Admitted.

Hint Extern 4 (IsTrunc _ (_ = _)) => eapply @istrunc_paths : typeclass_instances.

Class Funext.

Instance isequiv_compose A B C f g `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f) | 1000.
Admitted.

Section IsEquivHomotopic.
  Context (A B : Type) `(f : A -> B) `(g : A -> B) `{IsEquiv A B f} (h : forall x:A, f x = g x).
  Let sect := (fun b:B => inverse (h (@equiv_inv _ _ f _ b)) @ @eisretr _ _ f _ b).
  Let retr := (fun a:A => inverse (ap (@equiv_inv _ _ f _) (h a)) @ @eissect _ _ f _ a).
  Global Instance isequiv_homotopic : IsEquiv g | 10000
    := ( BuildIsEquiv _ _ g (@equiv_inv _ _ f _) sect retr).
End IsEquivHomotopic.

Instance trunc_succ A n `{IsTrunc n A} : IsTrunc (trunc_S n) A | 1000. Admitted.

Global Instance trunc_forall A n `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a) | 100.
Admitted.

Instance trunc_prod A B n `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Admitted.

Global Instance trunc_arrow n {A B : Type} `{IsTrunc n B} : IsTrunc n (A -> B) | 100.
Admitted.

Instance isequiv_pr1_contr {A} {P : A -> Type} `{forall a, IsTrunc minus_two (P a)}
: IsEquiv (@projT1 A P) | 100.
Admitted.

Instance trunc_sigma n A `{P : A -> Type} `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.
Admitted.

Global Instance trunc_trunc `{Funext} A m n : IsTrunc (trunc_S n) (IsTrunc m A) | 0.
Admitted.

Definition BiInv {A B} (f : A -> B) : Type
:= ( {g : B -> A & forall x, g (f x) = x} * {h : B -> A & forall x, f (h x) = x}).

Global Instance isprop_biinv {A B} (f : A -> B) : IsTrunc (trunc_S minus_two) (BiInv f) | 0.
Admitted.

Instance isequiv_path {A B : Type} (p : A = B)
: IsEquiv (transport (fun X:Type => X) p) | 0.
Admitted.

Class ReflectiveSubuniverse_internal :=
  { inO_internal : Type -> Type ;
    O : Type -> Type ;
    O_unit : forall T, T -> O T }.

Class ReflectiveSubuniverse :=
  ReflectiveSubuniverse_wrap : Funext -> ReflectiveSubuniverse_internal.
Global Existing Instance ReflectiveSubuniverse_wrap.

Class inO {fs : Funext} {subU : ReflectiveSubuniverse} (T : Type) :=
  isequiv_inO : inO_internal T.

Global Instance hprop_inO {fs : Funext} {subU : ReflectiveSubuniverse} (T : Type) : IsTrunc (trunc_S minus_two) (inO T) .
Admitted.

(* To avoid looping class resolution *)
Hint Mode IsEquiv - - + : typeclass_instances. 

Fail Definition equiv_O_rectnd {fs : Funext} {subU : ReflectiveSubuniverse}
           (P Q : Type) {Q_inO : inO_internal Q}
: IsEquiv (fun f : O P -> P => compose f (O_unit P)) := _.
