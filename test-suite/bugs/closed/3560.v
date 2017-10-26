
(* File reduced by coq-bug-finder from original input, then from 6236 lines to 1049 lines, then from 920 lines to 209 lines, then from 179 lines to 30 lines *)
(* coqc version trunk (August 2014) compiled on Aug 31 2014 10:12:32 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (437b91a3ffd7327975a129b95b24d3f66ad7f3e4) *)

Set Primitive Projections.
Set Implicit Arguments.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Notation "x * y" := (prod x y) : type_scope.
Record Equiv A B := { equiv_fun :> A -> B ; equiv_isequiv : forall P, P equiv_fun }.
Goal forall (A B : Type) (C : Type), Equiv (A -> B -> C) (A * B -> C).
Proof.
  intros.
  exists (fun u => fun x => u (fst x) (snd x)).
Abort.
