(* -*- coqdoc-prog-args: ("-g") -*- *)
Definition a := 0. #[ (* templatize *)  universes( template) ]
Inductive mysum (A B:Type) : Type :=
  | myinl : A -> mysum A B
  | myinr : B -> mysum A B.

#[local]Definition b := 1.
