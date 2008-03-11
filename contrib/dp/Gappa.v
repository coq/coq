Require Export ZArith.
Require Export Reals.

Inductive float :=
  | Fzero : float
  | Float (b : positive) (s : bool) (m : positive) (e : Z) : float.

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Lemma IZR_Z2R :
  forall x, IZR x = Z2R x.
Admitted.

Ltac get_float t :=
  let get_mantissa t :=
    let rec aux t :=
      match t with
      | 1%R => xH
      | 2%R => constr:(xO xH)
      | 3%R => constr:(xI xH)
      | (2 * ?v)%R =>
        let w := aux v in constr:(xO w)
      | (1 + 2 * ?v)%R =>
        let w := aux v in constr:(xI w)
      end in
    aux t in
  let get_float_rational s n d :=
    let rec aux t :=
      match t with
      | 2%R => xH
      | (2 * ?v)%R =>
        let w := aux v in
        eval vm_compute in (Psucc w)
      end in
    let e := aux d in
    let m := get_mantissa n in
    eval vm_compute in (Float 2 s m (Zneg e)) in
  let get_float_integer s t :=
    let rec aux m e :=
      match m with
      | xO ?v =>
        let u := eval vm_compute in (Zsucc e) in
        aux v u
      | _ => constr:(m, e)
      end in
    let m := get_mantissa t in
    let v := aux m Z0 in
    match v with
    | (?m, ?e) => eval vm_compute in (Float 2 s m e)
    end in
  match t with
  | 0%R => Fzero
  | (-?n * /?d)%R => get_float_rational true n d
  | (?n * /?d)%R => get_float_rational false n d
  | (-?n / ?d)%R => get_float_rational true n d
  | (?n / ?d)%R => get_float_rational false n d
  | (-?n)%R => get_float_integer true n
  | ?n => get_float_integer false n
  | _ => false
  end.

Definition FtoR radix (s : bool) m e :=
  let sm := if s then Zneg m else Zpos m in
  match e with
  | Zpos p => Z2R (sm * Zpower_pos (Zpos radix) p)
  | Z0 => Z2R sm
  | Zneg p => (Z2R sm / Z2R (Zpower_pos (Zpos radix) p))%R
  end.

Definition F2R f :=
  match f with
  | Fzero => R0
  | Float b s m e => FtoR b s m e
  end.

Ltac get_term t :=
  match get_float t with
  | false =>
    match t with
    | (?a + ?b)%R =>
      let a' := get_term a in
      let b' := get_term b in
      constr:(Rplus a' b')
    | ?e => e
    end
  | ?f =>constr:(F2R f)
  end.

Ltac gappar :=
  intros ; subst ;
  repeat
  match goal with
  | H: (?a <= ?e <= ?b)%R |- _ =>
    let a' := get_float a in
    let b' := get_float b in
    let e' := get_term e in
    change (F2R a' <= e' <= F2R b')%R in H
  | |- (?a <= ?e <= ?b)%R =>
    let a' := get_float a in
    let b' := get_float b in
    let e' := get_term e in
    change (F2R a' <= e' <= F2R b')%R
  end.

Ltac gappa2 :=
  gappar;
  gappa.

