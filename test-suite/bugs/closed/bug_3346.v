Monomorphic Inductive paths (A : Type) (a : A) : A -> Type := idpath : paths A a a.
(* This should fail *)
Fail Check paths nat O O : Prop.
