(* This example used to be in (at least) exponential time in the number of
   conjunctive types in the hypotheses before revision 11713 *)
(* Expected time < 1.50s *)

Goal
True/\True->
True/\True->
True/\True->
False/\False.

Time auto decomp.
