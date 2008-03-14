Require Export ZArith.
Require Export ZArithRing.

(* Cette tactique a pour objectif de remplacer toute instance
   de (POS (xI e)) ou de (POS (xO e)) par
   2*(POS e)+1  ou 2*(POS e), pour rendre les expressions plus
   � m�me d'�tre utilis�es par Ring, lorsque ces expressions contiennent
   des variables de type positive. *)
Ltac compute_POS :=
  match goal with
  |  |- context [(Zpos (xI ?X1))] =>
      let v := constr:X1 in
      match constr:v with
      | 1%positive => fail 1
      | _ =>  rewrite (BinInt.Zpos_xI v)
      end
  |  |- context [(Zpos (xO ?X1))] =>
      let v := constr:X1 in
      match constr:v with
      | 1%positive => fail 1
      | _ =>  rewrite (BinInt.Zpos_xO v)
      end
  end.

Goal forall x : positive, Zpos (xI (xI x)) = (4 * Zpos x + 3)%Z.
intros.
repeat compute_POS.
 ring.
Qed.
