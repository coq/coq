From Stdlib Require Import BinInt Lia.

Set Primitive Projections.
Record params := { width : Z }.
Definition p : params := Build_params 64.

Definition width' := width.
Set Printing All.

Lemma foo : width p = 0%Z -> width p = 0%Z.
  intros.

  assert_succeeds (enough True; [lia|]).

(*   H : @eq Z (width p) Z0 *)
(*   ============================ *)
(*   @eq Z (width p) Z0 *)

  change (width' p = 0%Z) in H;cbv [width'] in H.
  (* check that we correctly got the compat constant in H *)
  Fail match goal with H : ?l = _ |- ?l' = _ => constr_eq l l' end.

(*   H : @eq Z (width p) Z0 *)
(*   ============================ *)
(*   @eq Z (width p) Z0 *)

  assert_succeeds (enough True; [lia|]).

  lia.
  (* Tactic failure:  Cannot find witness. *)
Qed.
