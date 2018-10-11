
(* When doing Module Foo with Definition bar := ..., bar must be
   generated with the same polymorphism as Foo.bar. *)
Module Mono.
  Unset Universe Polymorphism.
  Module Type T.
    Parameter foo : Type.
  End T.

  Module Type F(A:T). End F.

  Set Universe Polymorphism.
  Module M : T with Definition foo := Type.
    Monomorphic Definition foo := Type.
  End M.
End Mono.

Module Poly.
  Set Universe Polymorphism.

  Module Type T.
    Parameter foo@{i|Set < i} : Type@{i}.
  End T.

  Module Type F(A:T). End F.

  Unset Universe Polymorphism.
  Module M : T with Definition foo := Set : Type.
    Polymorphic Definition foo := Set : Type.
  End M.
End Poly.
