Require Import ZArith Nnat Omega.
Open Scope Z_scope.

(** Test of the zify preprocessor for (R)Omega *)

(* More details in file PreOmega.v

   (r)omega with Z        : starts with zify_op
   (r)omega with nat      : starts with zify_nat
   (r)omega with positive : starts with zify_positive
   (r)omega with N        : starts with uses zify_N
   (r)omega with *        : starts zify (a saturation of the others)
*)

(* zify_op *)

Goal forall a:Z, Zmax a a = a.
intros.
omega with *.
Qed.

Goal forall a b:Z, Zmax a b = Zmax b a.
intros.
omega with *.
Qed.

Goal forall a b c:Z, Zmax a (Zmax b c) = Zmax (Zmax a b) c.
intros.
omega with *.
Qed.

Goal forall a b:Z, Zmax a b + Zmin a b = a + b.
intros.
omega with *.
Qed.

Goal forall a:Z, (Zabs a)*(Zsgn a) = a.
intros.
zify.
intuition; subst; omega. (* pure multiplication: omega alone can't do it *)
Qed.

Goal forall a:Z, Zabs a = a -> a >= 0.
intros.
omega with *.
Qed.

Goal forall a:Z, Zsgn a = a -> a = 1 \/ a = 0 \/ a = -1.
intros.
omega with *.
Qed.

(* zify_nat *)

Goal forall m: nat, (m<2)%nat -> (0<= m+m <=2)%nat.
intros.
omega with *.
Qed.

Goal forall m:nat, (m<1)%nat -> (m=0)%nat.
intros.
omega with *.
Qed.

Goal forall m: nat, (m<=100)%nat -> (0<= m+m <=200)%nat.
intros.
omega with *.
Qed.
(* 2000 instead of 200: works, but quite slow *)

Goal forall m: nat, (m*m>=0)%nat.
intros.
omega with *.
Qed.

(* zify_positive *)

Goal forall m: positive, (m<2)%positive -> (2 <= m+m /\ m+m <= 2)%positive.
intros.
omega with *.
Qed.

Goal forall m:positive, (m<2)%positive -> (m=1)%positive.
intros.
omega with *.
Qed.

Goal forall m: positive, (m<=1000)%positive -> (2<=m+m/\m+m <=2000)%positive.
intros.
omega with *.
Qed.

Goal forall m: positive, (m*m>=1)%positive.
intros.
omega with *.
Qed.

(* zify_N *)

Goal forall m:N, (m<2)%N -> (0 <= m+m /\ m+m <= 2)%N.
intros.
omega with *.
Qed.

Goal forall m:N, (m<1)%N -> (m=0)%N.
intros.
omega with *.
Qed.

Goal forall m:N, (m<=1000)%N -> (0<=m+m/\m+m <=2000)%N.
intros.
omega with *.
Qed.

Goal forall m:N, (m*m>=0)%N.
intros.
omega with *.
Qed.

(* mix of datatypes *)

Goal forall p, Z_of_N (N_of_nat (nat_of_N (Npos p))) = Zpos p.
intros.
omega with *.
Qed.


