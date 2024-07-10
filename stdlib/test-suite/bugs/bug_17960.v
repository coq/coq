From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

Parameter Znth : Z -> list Z -> Z.
Parameter Zlength : list Z -> Z.
Parameter max_unsigned : Z.

Goal forall j r N M row_ptr,
  Zlength row_ptr = N + 1 ->
  0 <= r ->
  r <= Znth 0 row_ptr ->
  Znth (N + 1 - 1) row_ptr <= max_unsigned ->
  0 <= j < N ->
  0 <= M ->
  0 <= N + 1 ->
  0 <= j + 1 < N + 1 ->
  0 <= j + 1 < N + 1 ->
  j + 1 <= j + 1 + 0 ->
  Znth (j + 1) row_ptr <= Znth (j + 1) row_ptr ->
  0 <= j + 1 < N + 1 ->
  0 <= j < N + 1 ->
  j + 0 < j + 1 ->
  0 <= j + 1 < N + 1 ->
  0 <= N < N + 1 ->
  j + 1 <= N + 0 -> Znth (j + 1) row_ptr <= M -> 0 <= j + 1 < N + 1 ->
  0 <= 0 < N + 1 ->
  0 + 0 < j + 1 ->
  0 <= j + 1 < N + 1 ->
  0 <= N + 1 - 1 < N + 1 ->
  j + 1 <= N + 1 - 1 + 0 ->
  Znth (j + 1) row_ptr <= Znth (N + 1 - 1) row_ptr ->
  0 <= j < N + 1 ->
  0 <= j < N + 1 ->
  j <= j + 0 ->
  Znth j row_ptr <= Znth j row_ptr ->
  0 <= j < N + 1 ->
  0 <= N < N + 1 ->
  j <= N + 0 ->
  Znth j row_ptr <= M ->
  0 <= j < N + 1 ->
  0 <= 0 < N + 1 ->
  j <= 0 + 0 ->
  Znth j row_ptr <= Znth 0 row_ptr -> 0 <= j < N + 1 -> 0 <= N + 1 - 1 < N + 1 ->
  j <= N + 1 - 1 + 0 ->
  Znth j row_ptr <= Znth (N + 1 - 1) row_ptr ->
  0 <= j < N + 1 ->
  0 <= j + 1 < N + 1 ->
  j <= j + 1 + 0 ->
  Znth j row_ptr <= Znth (j + 1) row_ptr ->
  0 <= N < N + 1 ->
  0 <= N < N + 1 ->
  N <= N + 0 ->
  M <= M ->
  0 <= N < N + 1 ->
  0 <= 0 < N + 1 ->
  0 + 0 < N ->
  0 <= N < N + 1 ->
  0 <= N + 1 - 1 < N + 1 ->
  N <= N + 1 - 1 + 0 ->
  M <= Znth (N + 1 - 1) row_ptr ->
  0 <= N < N + 1 -> 0 <= j + 1 < N + 1 -> j + 1 + 0 < N ->
  False.
Proof.
  Timeout 1 Fail lia. (* lia crashes. *)
Abort.
