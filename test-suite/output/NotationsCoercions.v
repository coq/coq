(* Tests about skipping a coercion vs using a notation involving a coercion *)

(* Skipping a coercion vs using a notation for the coercion itself
   (regression #11053 in 8.10 after PR #8890, addressed by PR #11090) *)

Module B.

Section Test.
Variables (A B : Type) (a : A) (b : B).
Variable c : A -> B.
Coercion c : A >-> B.
Notation COERCION := (c).
Check b = a. (* printed the same except in 8.10 *)
End Test.

End B.

Module C.

Record word := { rep: Type }.
Coercion rep : word >-> Sortclass.
Axiom myword: word.
Axiom foo: myword.
Notation "'(_' 'BitVec' '32)'" := (rep myword).
Check foo. (* printed with Bitvec from #8890 in 8.10 and 8.11, regression due to #11172 in 8.12 *)

End C.

(* Examples involving coercions to funclass *)

Module D.

Record R := { f :> nat -> nat }.
Axiom r : R.
Notation "#[ x  ]" := (f x).
Check #[ r ] 0. (* printed the same from 8.10 (due to #8890), but not 8.11 and 8.12 (due to #11090) *)
Notation "##[ x  ]" := (f x 0).
Check ##[ r ]. (* printed the same from 8.10 *)
Check #[ r ] 0. (* printed ##[ r ] from 8.10 *)

End D.

(* Same examples with a parameter *)

Module E.

Record R A := { f :> A -> A }.
Axiom r : R nat.
Notation "#[ x  ]" := (f nat x).
Check #[ r ] 0. (* printed the same from 8.10 (due to #8890), but not 8.11 and 8.12 (due to #11090) *)
Notation "##[ x  ]" := (f nat x 0).
Check ##[ r ]. (* printed the same from 8.10 *)
Check #[ r ] 0. (* printed ##[ r ] from 8.10 *)

End E.
