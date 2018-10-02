(* Should not be an anomaly as it was at some time in
   September/October 2014 but some "Disjunctive/conjunctive
   introduction pattern expected" error *)

Theorem t: True.
Fail destruct 0 as x.
