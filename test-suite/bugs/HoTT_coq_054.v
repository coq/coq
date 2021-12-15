Inductive Empty : Prop := .

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Arguments idpath {A a} , [A] a.

Definition idmap {A : Type} : A -> A := fun x => x.

Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => Empty
                 end)
: z = z'.
  destruct z, z', pq; exact idpath.
Defined.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Theorem ex2_8 {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B)
              (* Fortunately, this unifies properly *)
              (pq : match (x, y) with (inl x', inl y') => x' = y' | (inr x', inr y') => x' = y' | _ => Empty end) :
  let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in
  ap f (path_sum x y pq) = path_sum (f x) (f y)
     (* Coq appears to require *ALL* of the annotations *)
     ((match x as x return match (x, y) with
              (inl x', inl y') => x' = y'
            | (inr x', inr y') => x' = y'
            | _ => Empty
          end -> match (f x, f y) with
               | (inl x', inl y') => x' = y'
               | (inr x', inr y') => x' = y'
               | _ => Empty end with
           | inl x' => match y as y return match y with
                                               inl y' => x' = y'
                                             | _ => Empty
                                           end -> match f y with
                                                    | inl y' => g x' = y'
                                                    | _ => Empty end with
                         | inl y' => ap g
                         | inr y' => idmap
                       end
           | inr x' => match y as y return match y return Prop with
                                               inr y' => x' = y'
                                             | _ => Empty
                                           end -> match f y return Prop with
                                                    | inr y' => h x' = y'
                                                    | _ => Empty end with
                         | inl y' => idmap
                         | inr y' => ap h
                       end
       end) pq).
  destruct x; destruct y; destruct pq; reflexivity.
Qed.
(* Toplevel input, characters 1367-1374:
Error:
In environment
A : Type
B : Type
A' : Type
B' : Type
g : A -> A'
h : B -> B'
x : A + B
y : A + B
pq :
match x with
| inl x' => match y with
            | inl y' => x' = y'
            | inr _ => Empty
            end
| inr x' => match y with
            | inl _ => Empty
            | inr y' => x' = y'
            end
end
f :=
fun z : A + B =>
match z with
| inl z' => inl (g z')
| inr z' => inr (h z')
end : A + B -> A' + B'
x' : B
y0 : A + B
y' : B
The term "x' = y'" has type "Type" while it is expected to have type
"Prop" (Universe inconsistency). *)
