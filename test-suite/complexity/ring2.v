(* This example checks the efficiency of the abstract machine used by ring *)
(* Expected time < 1.00s *)

Require Import BinInt Zbool.

Definition Zadd x y :=
match x with
| 0%Z => y
| Zpos x' =>
    match y with
    | 0%Z => x
    | Zpos y' => Zpos (x' + y')
    | Zneg y' =>
        match (x' ?= y')%positive with
        | Eq => 0%Z
        | Lt => Zneg (y' - x')
        | Gt => Zpos (x' - y')
        end
    end
| Zneg x' =>
    match y with
    | 0%Z => x
    | Zpos y' =>
        match (x' ?= y')%positive with
        | Eq => 0%Z
        | Lt => Zpos (y' - x')
        | Gt => Zneg (x' - y')
        end
    | Zneg y' => Zneg (x' + y')
    end
end.


Require Import Ring.

Lemma Zth : ring_theory Z0 (Zpos xH) Zadd Z.mul Z.sub Z.opp (@eq Z).
Admitted.

Ltac Zcst t :=
  match isZcst t with
    true => t
  | _ => constr:(NotConstant)
  end.

Add Ring Zr : Zth
  (decidable Zeq_bool_eq, constants [Zcst]).

Open Scope Z_scope.
Infix "+" := Zadd : Z_scope.

Goal forall a, a+a+a+a+a+a+a+a+a+a+a+a+a = a*13.
Timeout 5 Time intro; ring.
