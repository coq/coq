(* Submitted by Houda Anoun *)

Module toto.
Tactic Definition titi:=Auto.
End toto.

Module ti.
Import toto.
Tactic Definition equal:=
Match Context With
[ |- ?1=?1]-> titi
| [ |- ?]-> Idtac.

End ti.

Import ti.
Definition simple:(a:nat) a=a.
Intro.
equal.
Qed.
