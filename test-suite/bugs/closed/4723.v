
Require Coq.Program.Tactics.

Record Matrix (m n : nat).

Definition kp {m n p q: nat} (A: Matrix m n) (B: Matrix p q):
  Matrix (m*p) (n*q). Admitted.

Fail Program Fact kp_assoc
        (xr xc yr yc zr zc: nat)
        (x: Matrix xr xc) (y: Matrix yr yc) (z: Matrix zr zc):
  kp x (kp y z) = kp (kp x y) z.

Ltac Obligation Tactic := admit.
Fail Program Fact kp_assoc
        (xr xc yr yc zr zc: nat)
        (x: Matrix xr xc) (y: Matrix yr yc) (z: Matrix zr zc):
  kp x (kp y z) = kp (kp x y) z.

Axiom cheat : forall {A}, A.
Obligation Tactic := apply cheat.

Program Fact kp_assoc
        (xr xc yr yc zr zc: nat)
        (x: Matrix xr xc) (y: Matrix yr yc) (z: Matrix zr zc):
  kp x (kp y z) = kp (kp x y) z.
admit.
Admitted.
