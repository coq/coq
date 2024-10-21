(* An example of decide equality which was failing due to a lhs dep into the rhs *)

Require Import BinNums PosDef.
Goal forall x y, {Pos.compare_cont Gt x y = Gt} + {Pos.compare_cont Gt x y <> Gt}.
intros.
decide equality.
Abort.
