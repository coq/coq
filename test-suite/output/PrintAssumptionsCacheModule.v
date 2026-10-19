(* Print Assumptions reuses traversals across queries in one environment.
   A constant sealed by a signature is traversed through its module's
   implementation, also from inside another module. *)

Axiom foo : nat.

Module Type T.
  Parameter bar : nat.
End T.

Module M : T.
  Module Hide.
    Definition x := foo.
  End Hide.
  Definition bar := Hide.x.
End M.

Module N (X : T) : T.
  Definition y := X.bar.
  Definition bar := y.
End N.

Module P := N M.

Definition use_m := M.bar.
Definition use_p := P.bar.

Print Assumptions M.bar.
Print Assumptions use_m.
Print Assumptions P.bar.
Print Assumptions use_p.

(* Opening a module leaves the global environment unchanged. *)
Module Inside.
  Print Assumptions M.bar.
  Print Assumptions use_m.
  Print Assumptions use_p.
End Inside.

Print Assumptions use_m.
Print Assumptions M.bar.
