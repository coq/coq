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
