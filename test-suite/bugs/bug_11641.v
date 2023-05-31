Require Import Ltac2.Ltac2.

Fail Ltac2 my_change1 (a : constr) (b : constr) :=
  change $a with $b.

Fail Ltac2 my_change2 (a:preterm) (b:constr) :=
  change $preterm:a with $b.

(* This is pretty bad, maybe $x should mean $pattern:x in patterns?
   Main question is if we allow preterm in pattern, is
   "fun x => let y := preterm:($x) in pattern:($preterm:y)"
   going to be confusing? (x must be constr, and we error at runtime??)

   Instead don't allow preterms, instead expose "pattern_of_preterm : preterm -> pattern",
   having runtime errors there seems more sensible than with the quotation.
 *)
Ltac2 my_change3 (a:pattern) (b:constr) :=
  change $pattern:a with $b.

Fail Ltac2 dummy x := preterm:($pattern:x).

Goal id True -> False.
  Fail match! goal with [ |- True -> False ] => () end.
  my_change3 pat:(id True) constr:(True).
  match! goal with [ |- True -> False ] => () end.

  Fail let a := preterm:(id True) in change $preterm:a with True.
Abort.
