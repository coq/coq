Require Import Coq.ZArith.BinInt Coq.omega.Omega Coq.micromega.Lia.

Set Primitive Projections.
Record params := { width : Z }.
Definition p : params := Build_params 64.

Set Printing All.

Goal width p = 0%Z -> width p = 0%Z.
  intros.

  assert_succeeds (enough True; [omega|]).
  assert_succeeds (enough True; [lia|]).

(*   H : @eq Z (width p) Z0 *)
(*   ============================ *)
(*   @eq Z (width p) Z0 *)

  change tt with tt in H.

(*   H : @eq Z (width p) Z0 *)
(*   ============================ *)
(*   @eq Z (width p) Z0 *)

  assert_succeeds (enough True; [lia|]).
  (* Tactic failure: <tactic closure> fails. *)
  (* assert_succeeds (enough True; [omega|]). *)
  (* Tactic failure: <tactic closure> fails. *)

  (* omega. *)
  (* Error: Omega can't solve this system *)

  lia.
  (* Tactic failure:  Cannot find witness. *)
Qed.
