Set Universe Polymorphism.
Set Warnings "+redundant-elimination-constraint".

Section Global.
  Sort g g'.

  Fail Constraint Prop -> Type.
  Fail Constraint Type -> Prop.
  Fail Constraint SProp -> g.

  Fail Constraint Type -> g.
  Fail Constraint g -> g.

  Constraint Prop -> g.
  Constraint g -> Prop.
  Fail Constraint g -> SProp.

  Polymorphic Axiom ad@{s;u} : forall A : Univ@{s;u}, A.

  Polymorphic Definition t@{s s';u v|s -> s'} (A : Univ@{s;u}) (B : Univ@{s';v}) : A := ad A.

  Fail Check t@{g g';Set Set}.
  Check t@{g Prop;Set Set}.
  Check t@{Prop g;Set Set}.
  Check t@{Type g;Set Set}.
  Check t@{g' g';Set Set}.
  Fail Check t@{g Type;Set Set}.
End Global.

Definition dominant@{Exn Test;|Prop -> Test, Exn -> Test} := tt.

Section Dominant.
  Sort Exn.

  Sort Test.
  Constraint Prop -> Test.
  Succeed Constraint Exn -> Test.

  Fail Polymorphic Definition test@{s;l|Prop -> s, Exn -> s} (A : Univ@{s;l}) : A := ad A.
End Dominant.

Module Syntax.
  Fail Definition foo@{u|Type -> Prop} := Type@{u}.
  Fail Definition foo'@{|Prop -> SProp} := Prop.

  Definition bar@{s;u|s -> Type} := Univ@{s;u}.
  Definition bar'@{s;u|Prop -> s} := Univ@{s;u}.

  Definition bar''@{s s';|s -> s', s' -> Prop} := Prop.
  Fail Definition bar'''@{s;|s -> Type, Prop -> s} := Prop.
End Syntax.

Inductive sum@{sl sr s;ul ur} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) : Univ@{s;max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Definition sum_elim@{sl sr s0 s0';ul ur v|s0 -> s0'}
  (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> Univ@{s0';v})
  (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.

Definition sum_sind := sum_elim@{Type Type Type SProp;_ _ _}.
Definition sum_rect := sum_elim@{Type Type Type Type;_ _ _}.
Definition sum_ind := sum_elim@{Type Type Type Prop;_ _ _}.

Definition or_ind := sum_elim@{Prop Prop Prop Prop;_ _ _}.
Definition or_sind := sum_elim@{Prop Prop Prop SProp;_ _ _}.
Fail Definition or_rect := sum_elim@{Prop Prop Prop Type;_ _ _}.

Definition sumor := sum@{Type Prop Type;_ _}.

Definition sumor_sind := sum_elim@{Type Prop Type SProp;_ _ _}.
Definition sumor_rect := sum_elim@{Type Prop Type Type;_ _ _}.
Definition sumor_ind := sum_elim@{Type Prop Type Prop;_ _ _}.

Fail Definition idT@{sl sr s;ul ur|} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Type;ul ur} A B :=
  match x return sum@{sl sr Type;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Fail Definition idP@{sl sr s;ul ur|} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Prop;ul ur} A B :=
  match x return sum@{sl sr Prop;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Fail Definition idS@{sl sr s;ul ur|} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr SProp;ul ur} A B :=
  match x return sum@{sl sr SProp;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Fail Definition idV@{sl sr s s';ul ur|} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr s';ul ur} A B :=
  match x return sum@{sl sr s';ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Definition idT@{sl sr s;ul ur|s -> Type} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Type;ul ur} A B :=
  match x return sum@{sl sr Type;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Definition idP@{sl sr s;ul ur|s -> Prop} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Prop;ul ur} A B :=
  match x return sum@{sl sr Prop;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Definition idS@{sl sr s;ul ur|s -> SProp} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr SProp;ul ur} A B :=
  match x return sum@{sl sr SProp;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Definition idV@{sl sr s;ul ur} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr s;ul ur} A B :=
  match x return sum@{sl sr s;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Inductive List'@{s s';l} (A : Univ@{s;l}) : Univ@{s';l} :=
| nil' : List' A
| cons' : A -> List' A -> List' A.

Arguments nil' {A}.
Arguments cons' {A} _ _.

Definition list'_elim@{s s0 s';l l'|s0 -> s'}
  (A : Univ@{s;l}) (P : List'@{s s0;l} A -> Univ@{s';l'})
  (fn : P nil') (fc : forall (x : A) (l : List' A), P l -> P (cons' x l)) :=
  fix F (l : List'@{s s0;l} A) : P l :=
    match l with
    | nil' => fn
    | cons' x l => fc x l (F l)
    end.

Fail Fixpoint list'_idT@{s s';l|} {A : Univ@{s;l}} (l : List'@{s s';l} A) : List'@{s Type;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idT l)
  end.

Fail Fixpoint list'_idP@{s s';l|} {A : Univ@{s;l}} (l : List'@{s s';l} A) : List'@{s Prop;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idP l)
  end.

Fail Fixpoint list'_idS@{s s';l|} {A : Univ@{s;l}} (l : List'@{s s';l} A) : List'@{s SProp;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idS l)
  end.

Fail Fixpoint list'_idV@{s s0 s';l l'|l <= l'} {A : Univ@{s;l}} (l : List'@{s s0;l} A) : List'@{s s';l'} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idV l)
  end.

Fixpoint list'_idT@{s s';l|s' -> Type} {A : Univ@{s;l}} (l : List'@{s s';l} A) : List'@{s Type;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idT l)
  end.

Fixpoint list'_idP@{s s';l|s' -> Prop} {A : Univ@{s;l}} (l : List'@{s s';l} A) {struct l} : List'@{s Prop;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idP l)
  end.

Fixpoint list'_idS@{s s';l|s' -> SProp} {A : Univ@{s;l}} (l : List'@{s s';l} A) : List'@{s SProp;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idS l)
  end.

Fixpoint list'_idV@{s s0 s';l l'|l <= l', s0 -> s'} {A : Univ@{s;l}} (l : List'@{s s0;l} A) : List'@{s s';l'} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idV l)
  end.
