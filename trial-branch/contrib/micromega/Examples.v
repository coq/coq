Require Import OrderedRing.
Require Import RingMicromega.
Require Import ZCoeff.
Require Import Refl.
Require Import ZArith.
Require Import List.
(*****)
Require Import NRing.
Require Import VarMap.
(*****)
(*Require Import Ring_polynom.*)
(*****)

Import OrderedRingSyntax.

Section Examples.

Variable R : Type.
Variables rO rI : R.
Variables rplus rtimes rminus: R -> R -> R.
Variable ropp : R -> R.
Variables req rle rlt : R -> R -> Prop.

Variable sor : SOR rO rI rplus rtimes rminus ropp req rle rlt.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (rplus x y).
Notation "x * y " := (rtimes x y).
Notation "x - y " := (rminus x y).
Notation "- x" := (ropp x).
Notation "x == y" := (req x y).
Notation "x ~= y" := (~ req x y).
Notation "x <= y" := (rle x y).
Notation "x < y" := (rlt x y).

Definition phi : Z -> R := gen_order_phi_Z 0 1 rplus rtimes ropp.

Lemma ZSORaddon :
  SORaddon 0 1 rplus rtimes rminus ropp req rle (* ring elements *)
           0%Z 1%Z Zplus Zmult Zminus Zopp (* coefficients *)
           Zeq_bool Zle_bool
           phi (fun x => x) (pow_N 1 rtimes).
Proof.
constructor.
exact (Zring_morph sor).
exact (pow_N_th 1 rtimes sor.(SORsetoid)).
apply (Zcneqb_morph sor).
apply (Zcleb_morph sor).
Qed.

Definition Zeval_formula :=
  eval_formula 0 rplus rtimes rminus ropp req rle rlt phi (fun x => x) (pow_N 1 rtimes).
Definition Z_In := S_In 0%Z Zeq_bool Zle_bool.
Definition Z_Square := S_Square 0%Z Zeq_bool Zle_bool.

(* Example: forall x y : Z, x + y = 0 -> x - y = 0 -> x < 0 -> False *)

Lemma plus_minus : forall x y : R, x + y == 0 -> x - y == 0 -> x < 0 -> False.
Proof.
intros x y.
Open Scope Z_scope.
(*****)
set (env := fun x y : R => Node (Leaf y) x (Empty _)).
(*****)
(*set (env := fun (x y : R) => x :: y :: nil).*)
(*****)
set (expr :=
 Build_Formula (PEadd (PEX Z 1) (PEX Z 2)) OpEq (PEc 0)
   :: Build_Formula (PEsub (PEX Z 1) (PEX Z 2)) OpEq (PEc 0)
      :: Build_Formula (PEX Z 1) OpLt (PEc 0) :: nil).
set (cert :=
   S_Add (S_Mult (S_Pos 0 Zeq_bool Zle_bool 2 (refl_equal true)) (Z_In 2))
     (S_Add (S_Ideal (PEc 1) (Z_In 1)) (S_Ideal (PEc 1) (Z_In 0)))).
change (make_impl (Zeval_formula (env x y)) expr False).
apply (check_formulas_sound sor ZSORaddon expr cert).
reflexivity.
Close Scope Z_scope.
Qed.

(* Example *)

Let four : R := ((1 + 1) * (1 + 1)).
Lemma Zdiscr :
  forall a b c x : R,
    a * (x * x) + b * x + c == 0 -> 0 <= b * b - four * a * c.
Proof.
Open Scope Z_scope.
(*****)
set (env := fun (a b c x : R) => Node (Node (Leaf x) b (Empty _)) a (Leaf c)).
(*****)
(*set (env := fun (a b c x : R) => a :: b :: c :: x:: nil).*)
(*****)
set (poly1 :=
     (Build_Formula
           (PEadd
              (PEadd (PEmul (PEX Z 1) (PEmul (PEX Z 4) (PEX Z 4)))
                 (PEmul (PEX Z 2) (PEX Z 4))) (PEX Z 3)) OpEq (PEc 0)) :: nil).
set (poly2 :=
     (Build_Formula
        (PEsub (PEmul (PEX Z 2) (PEX Z 2))
           (PEmul (PEmul (PEc 4) (PEX Z 1)) (PEX Z 3))) OpGe (PEc 0)) :: nil).
set (wit :=
    (S_Add (Z_In 0)
       (S_Add (S_Ideal (PEmul (PEc (-4)) (PEX Z 1)) (Z_In 1))
          (Z_Square
             (PEadd (PEmul (PEc 2) (PEmul (PEX Z 1) (PEX Z 4))) (PEX Z 2))))) :: nil).
intros a b c x.
change (make_impl (Zeval_formula (env a b c x)) poly1
  (make_conj (Zeval_formula (env a b c x)) poly2)).
apply (check_conj_formulas_sound sor ZSORaddon poly1 poly2 wit).
reflexivity.
Close Scope Z_scope.
Qed.

End Examples.

