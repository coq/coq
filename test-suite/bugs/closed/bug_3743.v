(* File reduced by coq-bug-finder from original input, then from 967 lines to 469 lines, then from 459 lines to 35 lines *)
(* coqc version trunk (October 2014) compiled on Oct 11 2014 1:13:41 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (d65496f09c4b68fa318783e53f9cd6d5c18e1eb7) *)
Require Export Coq.Setoids.Setoid.

Add Parametric Relation A
: A (@eq A)
    transitivity proved by transitivity
      as refine_rel.
(* Toplevel input, characters 20-118:
Anomaly: index to an anonymous variable. Please report. *)
