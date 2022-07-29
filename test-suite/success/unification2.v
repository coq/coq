(* A test on the order of treatment of conversion problems *)
(* See #16311 *)

Require Import Coq.Lists.List.
Import ListNotations.

Parameter symbol : Type.
Parameter production : Type.
Parameter prod_rhs_rev: production -> list symbol.

Definition future_of_prod prod dot_pos : list symbol :=
  (fix loop n lst :=
    match n with
    | O => lst
    | S x => match loop x lst with [] => [] | _::q => q end
    end)
  dot_pos (rev' (prod_rhs_rev prod)).
