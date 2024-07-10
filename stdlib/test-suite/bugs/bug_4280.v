From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Eqdep_dec.
Local Open Scope Z_scope.

Definition t := { n: Z | n > 1 }.

Program Definition two : t := 2.
Next Obligation. lia. Qed.

Program Definition t_eq (x y: t) : {x=y} + {x<>y} :=
  if Z.eq_dec (proj1_sig x) (proj1_sig y) then left _ else right _.
Next Obligation.
  destruct x as [x Px], y as [y Py]. simpl in e; subst y.
  f_equal. apply UIP_dec. decide equality.
Qed.
Next Obligation.
  congruence.
Qed.

Definition t_list_eq: forall (x y: list t), {x=y} + {x<>y}.
Proof. decide equality. apply t_eq. Defined.

Goal match t_list_eq (two::nil) (two::nil) with left _ => True | right _ => False end.
Proof. exact I. Qed.
