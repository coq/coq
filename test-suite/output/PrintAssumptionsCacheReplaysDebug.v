(* Print Assumptions reuses traversals across queries in one environment.
   The assumptions-cache debug flag reports each replay of an earlier
   query's traversal, so this file checks that the global environment stays
   the same across consecutive queries, and that replays happen only when it
   does. *)

Set Debug "assumptions-cache".

Axiom ax : nat.
Definition f := ax.
Definition g := f + 1.

(* Nothing cached yet: no replay. *)
Print Assumptions g.
(* Same environment: [g] is replayed. *)
Print Assumptions g.
(* Sentences that do not declare anything, such as Set, Check and Unset,
   keep the environment. *)
Set Printing All. Check f. Unset Printing All.
(* [f] was walked by the first query. *)
Print Assumptions f.

Definition h := g.
(* A new constant changes the environment: everything is walked again. *)
Print Assumptions h.
Print Assumptions g.

Module M.
  (* Opening a module adds nothing to the environment: both queries replay
     [g]. *)
  Print Assumptions g.
  Print Assumptions g.
End M.

(* Closing [M] adds it to the environment: the first query walks, the second
   replays [g]. *)
Print Assumptions g.
Print Assumptions g.
