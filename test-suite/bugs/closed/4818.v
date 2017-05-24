(* -*- mode: coq; coq-prog-args: ("-R" "." "Prob" "-top" "Product") -*- *)
(* File reduced by coq-bug-finder from original input, then from 391 lines to 77 lines, then from 857 lines to 119 lines, then from 1584 lines to 126 lines, then from 362 lines to 135 lines, then from 149 lines to 135 lines *)
(* coqc version 8.5pl1 (June 2016) compiled on Jun 9 2016 17:27:17 with OCaml 4.02.3
   coqtop version 8.5pl1 (June 2016) *)
Set Universe Polymorphism.

Inductive GCov (I : Type) : Type := | Foo : I -> GCov I.

Section Product.

Variables S IS : Type.
Variable locS : IS -> True.

Goal GCov (IS * S) -> GCov IS.
intros X0. induction X0; intros.
destruct i.
specialize (locS i).
clear -locS. 
destruct locS. Show Universes.
Admitted.

(*
Anomaly: Universe Product.5189 undefined. Please report.
*)
