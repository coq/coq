(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinNums PosDef IntDef FloatClass.

(** * Specification of floating-point arithmetic

This specification is mostly borrowed from the [IEEE754.Binary] module
of the Flocq library (see {{http://flocq.gforge.inria.fr/}}) *)

(** ** Inductive specification of floating-point numbers

Similar to [Flocq.IEEE754.Binary.full_float], but with no NaN payload. *)
Variant spec_float :=
  | S754_zero (s : bool)
  | S754_infinity (s : bool)
  | S754_nan
  | S754_finite (s : bool) (m : positive) (e : Z).

(** ** Parameterized definitions

[prec] is the number of bits of the mantissa including the implicit one;
[emax] is the exponent of the infinities.

For instance, Binary64 is defined by [prec = 53] and [emax = 1024]. *)
Section FloatOps.
  Variable prec emax : Z.

  Definition emin := Z.sub (Z.sub (Zpos 3) emax) prec.
  Definition fexp e := Z.max (Z.sub e prec) emin.

  Section Zdigits2.
    Fixpoint digits2_pos (n : positive) : positive :=
      match n with
      | xH => xH
      | xO p => Pos.succ (digits2_pos p)
      | xI p => Pos.succ (digits2_pos p)
      end.

    Definition Zdigits2 n :=
      match n with
      | Z0 => n
      | Zpos p => Zpos (digits2_pos p)
      | Zneg p => Zpos (digits2_pos p)
      end.
  End Zdigits2.

  Section ValidBinary.
    Definition canonical_mantissa m e :=
      Z.eqb (fexp (Z.add (Zpos (digits2_pos m)) e)) e.

    Definition bounded m e :=
      andb (canonical_mantissa m e) (Z.leb e (Z.sub emax prec)).

    Definition valid_binary x :=
      match x with
      | S754_finite _ m e => bounded m e
      | _ => true
      end.
  End ValidBinary.

  Section Iter.
    Context {A : Type}.
    Variable (f : A -> A).

    Fixpoint iter_pos (n : positive) (x : A) {struct n} : A :=
      match n with
      | xI n' => iter_pos n' (iter_pos n' (f x))
      | xO n' => iter_pos n' (iter_pos n' x)
      | xH => f x
      end.
  End Iter.

  Section Rounding.
    Inductive location := loc_Exact | loc_Inexact : comparison -> location.

    Record shr_record := { shr_m : Z ; shr_r : bool ; shr_s : bool }.

    Definition shr_1 mrs :=
      let '(Build_shr_record m r s) := mrs in
      let s := orb r s in
      match m with
      | Z0 => Build_shr_record Z0 false s
      | Zpos xH => Build_shr_record Z0 true s
      | Zpos (xO p) => Build_shr_record (Zpos p) false s
      | Zpos (xI p) => Build_shr_record (Zpos p) true s
      | Zneg xH => Build_shr_record Z0 true s
      | Zneg (xO p) => Build_shr_record (Zneg p) false s
      | Zneg (xI p) => Build_shr_record (Zneg p) true s
      end.

    Definition loc_of_shr_record mrs :=
      match mrs with
      | Build_shr_record _ false false => loc_Exact
      | Build_shr_record _ false true => loc_Inexact Lt
      | Build_shr_record _ true false => loc_Inexact Eq
      | Build_shr_record _ true true => loc_Inexact Gt
      end.

    Definition shr_record_of_loc m l :=
      match l with
      | loc_Exact => Build_shr_record m false false
      | loc_Inexact Lt => Build_shr_record m false true
      | loc_Inexact Eq => Build_shr_record m true false
      | loc_Inexact Gt => Build_shr_record m true true
      end.

    Definition shr mrs e n :=
      match n with
      | Zpos p => (iter_pos shr_1 p mrs, Z.add e n)
      | _ => (mrs, e)
      end.

    Definition shr_fexp m e l :=
      shr (shr_record_of_loc m l) e (Z.sub (fexp (Z.add (Zdigits2 m) e)) e).

    Definition round_nearest_even mx lx :=
      match lx with
      | loc_Exact => mx
      | loc_Inexact Lt => mx
      | loc_Inexact Eq => if Z.even mx then mx else Z.add mx (Zpos 1)
      | loc_Inexact Gt => Z.add mx (Zpos 1)
      end.

    Definition binary_round_aux sx mx ex lx :=
      let '(mrs', e') := shr_fexp mx ex lx in
      let '(mrs'', e'') := shr_fexp (round_nearest_even (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
      match shr_m mrs'' with
      | Z0 => S754_zero sx
      | Zpos m => if Z.leb e'' (Z.sub emax prec) then S754_finite sx m e'' else S754_infinity sx
      | _ => S754_nan
      end.

    Definition shl_align mx ex ex' :=
      match Z.sub ex' ex with
      | Zneg d => (Pos.iter xO mx d, ex')
      | _ => (mx, ex)
      end.

    Definition binary_round sx mx ex :=
      let '(mz, ez) := shl_align mx ex (fexp (Z.add (Zpos (digits2_pos mx)) ex))in
      binary_round_aux sx (Zpos mz) ez loc_Exact.

    Definition binary_normalize m e szero :=
      match m with
      | Z0 => S754_zero szero
      | Zpos m => binary_round false m e
      | Zneg m => binary_round true m e
      end.
  End Rounding.

  (** ** Define operations *)

  Definition SFopp x :=
    match x with
    | S754_nan => S754_nan
    | S754_infinity sx => S754_infinity (negb sx)
    | S754_finite sx mx ex => S754_finite (negb sx) mx ex
    | S754_zero sx => S754_zero (negb sx)
    end.

  Definition SFabs x :=
    match x with
    | S754_nan => S754_nan
    | S754_infinity sx => S754_infinity false
    | S754_finite sx mx ex => S754_finite false mx ex
    | S754_zero sx => S754_zero false
    end.

  Definition SFcompare f1 f2 :=
    match f1, f2 with
    | S754_nan , _ | _, S754_nan => None
    | S754_infinity s1, S754_infinity s2 =>
      Some match s1, s2 with
      | true, true => Eq
      | false, false => Eq
      | true, false => Lt
      | false, true => Gt
      end
    | S754_infinity s, _ => Some (if s then Lt else Gt)
    | _, S754_infinity s => Some (if s then Gt else Lt)
    | S754_finite s _ _, S754_zero _ => Some (if s then Lt else Gt)
    | S754_zero _, S754_finite s _ _ => Some (if s then Gt else Lt)
    | S754_zero _, S754_zero _ => Some Eq
    | S754_finite s1 m1 e1, S754_finite s2 m2 e2 =>
      Some match s1, s2 with
      | true, false => Lt
      | false, true => Gt
      | false, false =>
        match Z.compare e1 e2 with
        | Lt => Lt
        | Gt => Gt
        | Eq => Pos.compare_cont Eq m1 m2
        end
      | true, true =>
        match Z.compare e1 e2 with
        | Lt => Gt
        | Gt => Lt
        | Eq => CompOpp (Pos.compare_cont Eq m1 m2)
        end
      end
    end.

  Definition SFeqb f1 f2 :=
    match SFcompare f1 f2 with
    | Some Eq => true
    | _ => false
    end.

  Definition SFltb f1 f2 :=
    match SFcompare f1 f2 with
    | Some Lt => true
    | _ => false
    end.

  Definition SFleb f1 f2 :=
    match SFcompare f1 f2 with
    | Some (Lt | Eq) => true
    | _ => false
    end.

  Definition SFclassify f :=
    match f with
    | S754_nan => NaN
    | S754_infinity false => PInf
    | S754_infinity true => NInf
    | S754_zero false => PZero
    | S754_zero true => NZero
    | S754_finite false m _ =>
      if Z.eqb (Zpos (digits2_pos m)) prec then PNormal
      else PSubn
    | S754_finite true m _ =>
      if Z.eqb (Zpos (digits2_pos m)) prec then NNormal
      else NSubn
    end.

  Definition SFmul x y :=
    match x, y with
    | S754_nan, _ | _, S754_nan => S754_nan
    | S754_infinity sx, S754_infinity sy => S754_infinity (xorb sx sy)
    | S754_infinity sx, S754_finite sy _ _ => S754_infinity (xorb sx sy)
    | S754_finite sx _ _, S754_infinity sy => S754_infinity (xorb sx sy)
    | S754_infinity _, S754_zero _ => S754_nan
    | S754_zero _, S754_infinity _ => S754_nan
    | S754_finite sx _ _, S754_zero sy => S754_zero (xorb sx sy)
    | S754_zero sx, S754_finite sy _ _ => S754_zero (xorb sx sy)
    | S754_zero sx, S754_zero sy => S754_zero (xorb sx sy)
    | S754_finite sx mx ex, S754_finite sy my ey =>
      binary_round_aux (xorb sx sy) (Zpos (Pos.mul mx my)) (Z.add ex ey) loc_Exact
    end.

  Definition cond_Zopp (b : bool) m := if b then Z.opp m else m.

  Definition SFadd x y :=
    match x, y with
    | S754_nan, _ | _, S754_nan => S754_nan
    | S754_infinity sx, S754_infinity sy =>
      match sx, sy with true, true | false, false => x | _, _ => S754_nan end
    | S754_infinity _, _ => x
    | _, S754_infinity _ => y
    | S754_zero sx, S754_zero sy =>
      match sx, sy with true, true | false, false => x | _, _ => S754_zero false end
    | S754_zero _, _ => y
    | _, S754_zero _ => x
    | S754_finite sx mx ex, S754_finite sy my ey =>
      let ez := Z.min ex ey in
      binary_normalize (Z.add (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez)))))
        ez false
    end.

  Definition SFsub x y :=
    match x, y with
    | S754_nan, _ | _, S754_nan => S754_nan
    | S754_infinity sx, S754_infinity sy =>
      match sx, sy with true, false | false, true => x | _, _ => S754_nan end
    | S754_infinity _, _ => x
    | _, S754_infinity sy => S754_infinity (negb sy)
    | S754_zero sx, S754_zero sy =>
      match sx, sy with true, false | false, true => x | _, _ => S754_zero false end
    | S754_zero _, S754_finite sy my ey => S754_finite (negb sy) my ey
    | _, S754_zero _ => x
    | S754_finite sx mx ex, S754_finite sy my ey =>
      let ez := Z.min ex ey in
      binary_normalize (Z.sub (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez)))))
        ez false
    end.

  Definition new_location_even nb_steps k :=
    if Z.eqb k Z0 then loc_Exact
    else loc_Inexact (Z.compare (Z.mul (Zpos 2) k) nb_steps).

  Definition new_location_odd nb_steps k :=
    if Z.eqb k Z0 then loc_Exact
    else
      loc_Inexact
      match Z.compare (Z.add (Z.mul (Zpos 2) k) (Zpos 1)) nb_steps with
      | Lt => Lt
      | Eq => Lt
      | Gt => Gt
      end.

  Definition new_location nb_steps :=
    if Z.even nb_steps then new_location_even nb_steps else new_location_odd nb_steps.

  Definition SFdiv_core_binary m1 e1 m2 e2 :=
    let d1 := Zdigits2 m1 in
    let d2 := Zdigits2 m2 in
    let e' := Z.min (fexp (Z.sub (Z.add d1 e1) (Z.add d2 e2))) (Z.sub e1 e2) in
    let s := Z.sub (Z.sub e1 e2) e' in
    let m' :=
      match s with
      | Zpos _ => Z.shiftl m1 s
      | Z0 => m1
      | Zneg _ => Z0
      end in
    let '(q, r) := Z.div_eucl m' m2 in
    (q, e', new_location m2 r).

  Definition SFdiv x y :=
    match x, y with
    | S754_nan, _ | _, S754_nan => S754_nan
    | S754_infinity sx, S754_infinity sy => S754_nan
    | S754_infinity sx, S754_finite sy _ _ => S754_infinity (xorb sx sy)
    | S754_finite sx _ _, S754_infinity sy => S754_zero (xorb sx sy)
    | S754_infinity sx, S754_zero sy => S754_infinity (xorb sx sy)
    | S754_zero sx, S754_infinity sy => S754_zero (xorb sx sy)
    | S754_finite sx _ _, S754_zero sy => S754_infinity (xorb sx sy)
    | S754_zero sx, S754_finite sy _ _ => S754_zero (xorb sx sy)
    | S754_zero sx, S754_zero sy => S754_nan
    | S754_finite sx mx ex, S754_finite sy my ey =>
      let '(mz, ez, lz) := SFdiv_core_binary (Zpos mx) ex (Zpos my) ey in
      binary_round_aux (xorb sx sy) mz ez lz
    end.

  Definition SFsqrt_core_binary m e :=
    let d := Zdigits2 m in
    let e' := Z.min (fexp (Z.div2 (Z.add (Z.add d e) (Zpos 1)))) (Z.div2 e) in
    let s := Z.sub e (Z.mul (Zpos 2) e') in
    let m' :=
      match s with
      | Zpos p => Z.shiftl m s
      | Z0 => m
      | Zneg _ => Z0
      end in
    let (q, r) := Z.sqrtrem m' in
    let l :=
      if Z.eqb r Z0 then loc_Exact
      else loc_Inexact (if Z.leb r q then Lt else Gt) in
    (q, e', l).

  Definition SFsqrt x :=
    match x with
    | S754_nan => S754_nan
    | S754_infinity false => x
    | S754_infinity true => S754_nan
    | S754_finite true _ _ => S754_nan
    | S754_zero _ => x
    | S754_finite false mx ex =>
      let '(mz, ez, lz) := SFsqrt_core_binary (Zpos mx) ex in
      binary_round_aux false mz ez lz
    end.

  Definition SFnormfr_mantissa f :=
    match f with
    | S754_finite _ mx ex =>
      if Z.eqb ex (Z.opp prec) then Npos mx else N0
    | _ => N0
    end.

  Definition SFldexp f e :=
    match f with
    | S754_finite sx mx ex => binary_round sx mx (Z.add ex e)
    | _ => f
    end.

  Definition SFfrexp f :=
    match f with
    | S754_finite sx mx ex =>
      if Z.leb prec (Zpos (digits2_pos mx)) then
        (S754_finite sx mx (Z.opp prec), Z.add ex prec)
      else
        let d := Z.sub prec (Zpos (digits2_pos mx)) in
        (S754_finite sx (Pos.iter xO mx (Z.to_pos d)) (Z.opp prec), Z.sub (Z.add ex prec) d)
    | _ => (f, Z.sub (Z.mul (Zneg 2) emax) prec)
    end.

  Definition SFone := binary_round false 1 Z0.

  Definition SFulp x := SFldexp SFone (fexp (snd (SFfrexp x))).

  Definition SFpred_pos x :=
    match x with
    | S754_finite _ mx _ =>
      let d :=
        if Pos.eqb mx~0 (Pos.iter xO xH (Z.to_pos prec)) then
          SFldexp SFone (fexp (Z.sub (snd (SFfrexp x)) (Zpos 1)))
        else
          SFulp x in
      SFsub x d
    | _ => x
    end.

  Definition SFmax_float :=
    S754_finite false (Pos.sub (Pos.iter xO xH (Z.to_pos prec)) 1) (Z.sub emax prec).

  Definition SFsucc x :=
    match x with
    | S754_zero _ => SFldexp SFone emin
    | S754_infinity false => x
    | S754_infinity true => SFopp SFmax_float
    | S754_nan => x
    | S754_finite false _ _ => SFadd x (SFulp x)
    | S754_finite true _ _ => SFopp (SFpred_pos (SFopp x))
    end.

  Definition SFpred f := SFopp (SFsucc (SFopp f)).
End FloatOps.
