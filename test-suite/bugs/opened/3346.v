(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter") -*- *)
Monomorphic Inductive paths (A : Type) (a : A) : A -> Type := idpath : paths A a a.
(* This should fail with -indices-matter *)
Check paths nat O O : Prop.
