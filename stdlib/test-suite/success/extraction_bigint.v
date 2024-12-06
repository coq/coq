(** Test extraction of big integers using zarith *)

From Stdlib Require Extraction ExtrOcamlZBigInt.
From Stdlib Require Import Bool Arith ZArith List.
Import ListNotations.

Definition from_sumbool {P Q} (p : {P} + {Q}) : bool :=
  match p with
  | left _ => true
  | right _ => false
  end.

Definition tests_Pos : list bool :=
  [ 1 =? 1
  ; Pos.succ 3 =? 4
  ; Pos.pred 3 =? 2
  ; 1 + 2 =? 3
  ; 6 - 2 =? 4
  ; 3 - 3 =? 1
  ; 3 - 6 =? 1
  ; 3 * 4 =? 12
  ; Pos.min 2 3 =? 2
  ; Pos.max 2 3 =? 3
  ; Pos.eqb 1 1
  ; Pos.shiftl 2 3 =? 16
  ; Pos.shiftr 4 2 =? 1
  ; from_sumbool (Pos.eq_dec 1 1)
  ; negb (from_sumbool (Pos.eq_dec 1 2))
  ]%positive.

Definition test_positive : { b | b = true } := exist _ (forallb (fun x => x) tests_Pos) eq_refl.

Definition eq_N2 (x y : N * N) : bool :=
  ((fst x =? fst y) && (snd x =? snd y))%N.

Definition tests_N : list bool :=
  [ 0 =? 0
  ; N.succ 3 =? 4
  ; N.pred 3 =? 2
  ; 1 + 2 =? 3
  ; 6 - 2 =? 4
  ; 3 - 4 =? 0
  ; 3 * 4 =? 12
  ; N.min 2 3 =? 2
  ; N.max 2 3 =? 3
  ; N.eqb 1 1
  ; 11 / 2 =? 5
  ; 11 mod 3 =? 2
  ; N.shiftl 2 3 =? 16
  ; N.shiftr 4 2 =? 1
  ; negb (N.eqb 0 1)
  ; from_sumbool (N.eq_dec 0 0)
  ; negb (from_sumbool (N.eq_dec 0 1))
  ; Z.to_N 3 =? 3
  ; eq_N2 (N.div_eucl 11 0) (0, 11)
  ; eq_N2 (N.div_eucl 11 3) (3, 2)
  ]%N.

Definition test_N : { b | b = true } := exist _ (forallb (fun x => x) tests_N) eq_refl.

Definition eq_Z2 (x y : Z * Z) : bool :=
  ((fst x =? fst y) && (snd x =? snd y))%Z.

Definition tests_Z : list bool :=
  [ 0 =? 0
  ; Z.succ 3 =? 4
  ; Z.pred 3 =? 2
  ; 1 + 2 =? 3
  ; 1 + (-4) =? -3
  ; 3 - 4 =? -1
  ; 3 - (-4) =? 7
  ; (-3) * (-4) =? 12
  ; (-3) * 4 =? -12
  ; Z.opp 3 =? -3
  ; Z.opp (-3) =? 3
  ; Z.abs 3 =? 3
  ; Z.abs (-3) =? 3
  ; Z.min (-3) 3 =? -3
  ; Z.max (-3) 3 =? 3
  ; Z.eqb 1 1
  ; 11 / 0 =? 0
  ; 11 / 2 =? 5
  ; (-11) / 2 =? -6
  ; 11 / (-2) =? -6
  ; (-11) / (-2) =? 5
  ; 11 mod 0 =? 11
  ; 11 mod 3 =? 2
  ; (-11) mod 3 =? 1
  ; 11 mod (-3) =? -1
  ; (-11) mod (-3) =? -2
  ; Z.shiftl 2 3 =? 16
  ; Z.shiftl 2 (-1) =? 1
  ; Z.shiftr 4 2 =? 1
  ; Z.shiftr 4 (-3) =? 32
  ; negb (Z.eqb 0 1)
  ; from_sumbool (Z.eq_dec 0 0)
  ; negb (from_sumbool (Z.eq_dec 0 1))
  ; Z.of_N 3 =? 3
  ; eq_Z2 (Z.div_eucl 11 0) (0, 11)
  ; eq_Z2 (Z.div_eucl 11 3) (3, 2)
  ; eq_Z2 (Z.div_eucl (-11) 3) (-4, 1)
  ; eq_Z2 (Z.div_eucl 11 (-3)) (-4, -1)
  ; eq_Z2 (Z.div_eucl (-11) (-3)) (3, -2)
  ]%Z.

Definition test_Z : { b | b = true } := exist _ (forallb (fun x => x) tests_Z) eq_refl.

Extraction TestCompile test_positive test_Z test_N.
