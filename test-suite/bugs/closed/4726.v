Set Universe Polymorphism.

Definition le@{i j} : Type@{j} :=
  (fun A : Type@{j} => A)
  (unit : Type@{i}).  
Definition eq@{i j} : Type@{j} := let x := le@{i j} in le@{j i}.

Record Inj@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{j} :=
  { inj : A }.

Monomorphic Universe u1.
Let ty1 : Type@{u1} := Set.
Check Inj@{Set u1}.
(* Would fail with univ inconsistency if the universe was minimized *)

Record Inj'@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{j} :=
  { inj' : A; foo : Type@{j} := eq@{i j} }.
Fail Check Inj'@{Set u1}. (* Do not drop constraint i = j *)
Check Inj'@{Set Set}.
