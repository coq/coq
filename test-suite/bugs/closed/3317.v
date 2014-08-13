Set Implicit Arguments. 
Module A.
  Set Universe Polymorphism.
  Set Primitive Projections.
  Set Asymmetric Patterns.
  Inductive paths {A} (x : A) : A -> Type := idpath : paths x x
                                                            where "x = y" := (@paths _ x y) : type_scope.
  Record sigT {A : Type} (P : A -> Type) := existT { projT1 : A; projT2 : P projT1 }.
  Arguments existT {A} _ _ _.
  Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
    match p with idpath => u end.
  Notation "x .1" := (projT1 x) (at level 3).
  Notation "x .2" := (projT2 x) (at level 3).
  Notation "( x ; y )" := (existT _ x y).
  Set Printing All.
  Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
             (pq : sigT (fun p : u.1 = v.1 => transport _ p u.2 = v.2))
  : u = v
    := match pq with
         | existT p q =>
           match u, v return (forall p0 : (u.1 = v.1), (transport P p0 u.2 = v.2) -> (u=v)) with
             | (x;y), (x';y') => fun p1 (q1 : transport P p1 (existT P x y).2 = (existT P x' y').2) =>
                                   match p1 in (_ = x'') return (forall y'', (transport _ p1 y = y'') -> (x;y)=(x'';y'')) with
                                     | idpath => fun y' (q2 : transport _ (@idpath _ _) y = y') =>
                                                   match q2 in (_ = y'') return (x;y) = (x;y'') with
                                                     | idpath => @idpath _ _
                                                   end
                                   end y' q1
           end p q
       end.
  (* Toplevel input, characters 341-357:
Error:
In environment
A : Type
P : forall _ : A, Type
u : @sigT A P
v : @sigT A P
pq :
@sigT (@paths A (projT1 u) (projT1 v))
  (fun p : @paths A (projT1 u) (projT1 v) =>
   @paths (P (projT1 v)) (@transport A P (projT1 u) (projT1 v) p (projT2 u))
     (projT2 v))
p : @paths A (projT1 u) (projT1 v)
q :
@paths (P (projT1 v)) (@transport A P (projT1 u) (projT1 v) p (projT2 u))
  (projT2 v)
x : A
y : P x
x' : A
y' : P x'
p1 : @paths A (projT1 (@existT A P x y)) (projT1 (@existT A P x' y'))
The term "projT2 (@existT A P x y)" has type "P (projT1 (@existT A P x y))"
while it is expected to have type "P (projT1 (@existT A P x y))".
   *)
End A.

Module B.
  Set Universe Polymorphism.
  Set Primitive Projections.
  Set Asymmetric Patterns.
  Inductive paths {A} (x : A) : A -> Type := idpath : paths x x
                                                            where "x = y" := (@paths _ x y) : type_scope.
  Record sigT {A : Type} (P : A -> Type) := existT { projT1 : A; projT2 : P projT1 }.
  Arguments existT {A} _ _ _.
  Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
    match p with idpath => u end.
  Notation "x .1" := (projT1 x) (at level 3).
  Notation "x .2" := (projT2 x) (at level 3).
  Notation "( x ; y )" := (existT _ x y).
  Set Printing All.

  Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
             (pq : sigT (fun p : u.1 = v.1 => transport _ p u.2 = v.2))
  : u = v.
  Proof.
    destruct u as [x y].
    destruct v. (* Toplevel input, characters 0-11:
Error: Illegal application:
The term "transport" of type
 "forall (A : Type) (P : forall _ : A, Type) (x y : A)
    (_ : @paths A x y) (_ : P x), P y"
cannot be applied to the terms
 "A" : "Type"
 "P" : "forall _ : A, Type"
 "projT1 (@existT A P x y)" : "A"
 "projT1 v" : "A"
 "p" : "@paths A (projT1 (@existT A P x y)) (projT1 v)"
 "projT2 (@existT A P x y)" : "P (projT1 (@existT A P x y))"
The 5th term has type "@paths A (projT1 (@existT A P x y)) (projT1 v)"
which should be coercible to
 "@paths A (projT1 (@existT A P x y)) (projT1 v)".
                 *)
  Abort.
End B.
