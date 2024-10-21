Require Import TestSuite.funind.
Ltac u a b := functional induction a as b.
Print u.
