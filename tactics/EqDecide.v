(****************************************************************************)
(*                                EqDecide.v                                *)
(*     A tactic for deciding propositional equality on inductive types      *)
(*                             by Eduardo Gimenez                           *)
(****************************************************************************)

(*i $Id$ i*)

Declare ML Module "equality" "eqdecide".


Grammar tactic simple_tactic : ast :=
  EqDecideRuleG1 
   [ "Decide"  "Equality" constrarg($com1) constrarg($com2) ] -> 
   [ (DecideEquality $com1 $com2) ]

| EqDecideRuleG2 
   [ "Decide" "Equality" ] -> [ (DecideEquality) ]

| CompareRule 
   [ "Compare" constrarg($com1) constrarg($com2) ] -> [ (Compare $com1 $com2) ].


Syntax tactic level 0:
  EqDecideRulePP1 
   [ <<(DecideEquality)>> ] -> [ "Decide Equality" ]

| EqDecideRulePP2 
   [ <<(DecideEquality $com1 $com2)>> ] -> 
   [ "Decide Equality" [1 2] $com1 [1 2] $com2 ]

| ComparePP 
   [ <<(Compare $com1 $com2)>> ] -> [ "Compare" [1 2] $com1 [1 2] $com2 ].
