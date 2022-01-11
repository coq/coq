(* A reduced form of bug #15455 *)

Record R := { f {Hp : 0 = 0} (Hq : 0 = 0) : bool }.
Arguments f _ Hp Hq, _ {Hp} Hq.
Check fun x => x.(f) eq_refl eq_refl.
