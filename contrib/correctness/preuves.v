
(* Quelques preuves sur des programmes simples,
 * juste histoire d'avoir un petit bench.
 *)

Require Programs.
Require Omega.

Prog Variable x : Z ref.
Prog Variable y : Z ref.
Prog Variable z : Z ref.
Prog Variable i : Z ref.
Prog Variable j : Z ref.
Prog Variable n : Z ref.
Prog Variable m : Z ref.
Variable r : Z.
Variable N : Z.
Prog Variable t : array N of Z.


(**********************************************************************)

Correctness echange
  { `0 <= i < N` /\ `0 <= j < N` }
  begin
    state B;
    x := t[!i]; t[!i] := t[!j]; t[!j] := !x;
    assert { t#[i] = t@B#[j] /\ t#[j] = t@B#[i] }
  end.
Proof.
Auto.
Assumption.
Assumption.
Elim HH_6; Auto.
Elim HH_6; Auto.
Save.

  
(**********************************************************************)

(*
 *   while x <= y do x := x+1 done { y < x }
 *)

Correctness incrementation
  while (Z_le_gt_dec !x !y) do
    { invariant True variant (Zminus (Zs y) x) }
    x := (Zs !x)
  done
  { `y < x` }.
Proof.
Exact (Zwf_well_founded `0`).
Unfold Zwf. Omega.
Exact I.
Save.


(************************************************************************)

Correctness pivot1
  begin
    while (Z_lt_ge_dec !i r) do
      { invariant True variant (Zminus (Zs r) i) } i := (Zs !i)
    done;
    while (Z_lt_ge_dec r !j) do
      { invariant True variant (Zminus (Zs j) r) } j := (Zpred !j)
    done
  end
  { `j <= r` /\ `r <= i` }.
Proof.
Exact (Zwf_well_founded `0`).
Unfold Zwf. Omega.
Exact I.
Exact (Zwf_well_founded `0`).
Unfold Zwf. Unfold Zpred. Omega.
Exact I.
Omega.
Save.



