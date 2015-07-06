Set Universe Polymorphism.
Notation Type0 := Set.

Definition Type1 := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Notation Contr := (IsTrunc -2).
Notation IsHProp := (IsTrunc -1).

Monomorphic Axiom dummy_funext_type : Type0.
Monomorphic Class Funext := { dummy_funext_value : dummy_funext_type }.

Inductive Unit : Type1 :=
    tt : Unit.

Record TruncType (n : trunc_index) := BuildTruncType {
  trunctype_type : Type ;
  istrunc_trunctype_type : IsTrunc n trunctype_type
}.

Arguments BuildTruncType _ _ {_}.

Coercion trunctype_type : TruncType >-> Sortclass.

Notation "n -Type" := (TruncType n) (at level 1) : type_scope.
Notation hProp := (-1)-Type.

Notation BuildhProp := (BuildTruncType -1).

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Arguments tr {n A} a.

Global Instance istrunc_truncation (n : trunc_index) (A : Type@{i})
: IsTrunc@{j} n (Trunc@{i} n A).
Admitted.

Definition Trunc_ind {n A}
  (P : Trunc n A -> Type) {Pt : forall aa, IsTrunc n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => fun _ => f a end Pt).
Definition merely (A : Type@{i}) : hProp@{i} := BuildhProp (Trunc -1 A).
Definition cconst_factors_contr `{Funext}  {X Y : Type} (f : X -> Y)
           (P : Type) `{Pc : X -> Contr P}
           (g : X -> P) (h : P -> Y) (p : h o g == f)
: Unit.
Proof.
  assert (merely X -> IsHProp P) by admit.
  refine (let g' := Trunc_ind (fun _ => P) g : merely X -> P in _);
    [ assumption.. | ].
  Fail pose (g' := Trunc_ind (fun _ => P) g : merely X -> P).
