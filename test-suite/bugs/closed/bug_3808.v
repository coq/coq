Unset Strict Universe Declaration.
Inductive Foo : (let enforce := (fun x => x) : Type@{j} -> Type@{i} in Type@{i})
  := foo : Foo.
