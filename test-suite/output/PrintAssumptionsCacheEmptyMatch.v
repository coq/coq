(* Print Assumptions reuses traversals across queries in one environment.
   A match on an empty inductive applied to an axiom records which object
   used it and to prove what. That record belongs to the query, so each
   query must report it, whether the object is queried directly or reached
   through an object an earlier query already traversed. *)

Inductive empty : Prop := .
Axiom impossible : empty.

Module Plain.
  Definition probe : False := match impossible with end.
  Definition anc : False := probe.
  Definition top1 : False := anc.
  Definition top2 : False := anc.
  Print Assumptions top1.
  Print Assumptions top2.
  Print Assumptions anc.
  Print Assumptions probe.
  Print Assumptions top1.
End Plain.

Module BlockMember.
  Inductive b1 : Prop := mk1 : (match impossible return Prop with end) -> b1
  with b2 : Prop := mk2 : b2.
  Definition use_b2 := mk2.
  Definition t1 := use_b2.
  Definition t2 := use_b2.
  Print Assumptions t1.
  Print Assumptions t2.
  Print Assumptions use_b2.
  Print Assumptions b1.
  Print Assumptions mk2.
  Print Assumptions t1.
End BlockMember.

Module AxiomFirst.
  (* The same axiom reached through an ordinary reference before the
     empty match and after it. *)
  Axiom w : nat.
  Axiom z : (fun _ : nat => empty) w.
  Definition plain_z : empty := z.
  Definition probe_z : False := match z with end.
  Definition both1 : empty * False := (plain_z, probe_z).
  Definition both2 : False * empty := (probe_z, plain_z).
  Print Assumptions plain_z.
  Print Assumptions both1.
  Print Assumptions both2.
  Print Assumptions probe_z.
  Print Assumptions both2.
End AxiomFirst.
