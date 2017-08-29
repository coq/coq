(* Testing forward reasoning *)

Goal 0=0.
Fail assert (_ = _).
eassert (_ = _)by reflexivity.
eassumption.
Qed.

Goal 0=0.
Fail set (S ?[nl]).
eset (S ?[n]).
remember (S ?n) as x.
instantiate (n:=0).
Fail remember (S (S _)).
eremember (S (S ?[x])).
instantiate (x:=0).
reflexivity.
Qed.

(* Don't know if it is good or not but the compatibility tells that
   the asserted goal to prove is subject to beta-iota but not the
   asserted hypothesis *)

Goal True.
assert ((fun x => x) False).
Fail match goal with |- (?f ?a) => idtac end. (* should be beta-iota reduced *)
2:match goal with _: (?f ?a) |- _ => idtac end. (* should not be beta-iota reduced *)
Abort.

