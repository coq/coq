
(* Quelques preuves sur des programmes simples,
 * juste histoire d'avoir un petit bench.
 *)

Require Correctness.
Require Omega.

Global Variable x : Z ref.
Global Variable y : Z ref.
Global Variable z : Z ref.
Global Variable i : Z ref.
Global Variable j : Z ref.
Global Variable n : Z ref.
Global Variable m : Z ref.
Variable r : Z.
Variable N : Z.
Global Variable t : array N of Z.

(**********************************************************************)

Require Exchange.
Require ArrayPermut.

Correctness swap
  fun (N:Z)(t:array N of Z)(i,j:Z) ->
    { `0 <= i < N` /\ `0 <= j < N` }
    (let v = t[i] in
     begin
       t[i] := t[j];
       t[j] := v
     end)
    { (exchange t t@ i j) }.
Proof.
Auto with datatypes.
Save.

Correctness downheap
  let rec downheap (N:Z)(t:array N of Z) : unit { variant `0` } =
    (swap N t 0 0) { True }
.

(**********************************************************************)

Global Variable x : Z ref.
Debug on.
Correctness assign0 (x := 0) { `x=0` }.
Save.

(**********************************************************************)

Global Variable i : Z ref.
Debug on.
Correctness assign1 { `0 <= i` } (i := !i + 1) { `0 < i` }.
Omega.
Save.

(**********************************************************************)

Global Variable i : Z ref.
Debug on.
Correctness if0 { `0 <= i` } (if !i>0 then i:=!i-1 else tt) { `0 <= i` }.
Omega.
Save.

(**********************************************************************)

Global Variable i : Z ref.
Debug on.
Correctness assert0 { `0 <= i` } begin assert { `i=2` }; i:=!i-1 end { `i=1` }.

(**********************************************************************)

Correctness echange
  { `0 <= i < N` /\ `0 <= j < N` }
  begin
    label B;
    x := t[!i]; t[!i] := t[!j]; t[!j] := !x;
    assert { #t[i] = #t@B[j] /\ #t[j] = #t@B[i] }
  end.
Proof.
Auto with datatypes.
Save.

  
(**********************************************************************)

(*
 *   while x <= y do x := x+1 done { y < x }
 *)

Correctness incrementation
  while !x < !y do
    { invariant True variant `(Zs y)-x` }
    x := !x + 1
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



