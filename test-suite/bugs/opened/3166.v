Set Asymmetric Patterns.

Section eq.
  Let A := { X : Type & X }.
  Let B := (fun x : A => projT1 x).
  Let T := (fun (a' : A) (b' : B a') => projT2 a' = b').
  Let T' := T.
  Let t1T := (fun _ : A => unit).
  Let f1 := (fun x (_ : t1T x) => projT2 x).
  Let t1 := (fun x (y : t1T x) => @eq_refl (projT1 x) (projT2 x)).
  Let t1T' := t1T.
  Let f1' := f1.
  Let t1' := t1.

  Theorem eq_matches_commute
          a' b' (t' : T a' b')
          (rta : forall b'', T' a' b'' -> A)
          (rtb : forall b'' t'', B (rta b'' t''))
          (rt1 : forall y, T _ (rtb (f1' a' y) (@t1' a' y)))
          (R : forall (b : B (rta b' t')), T _ b -> Type)
          (r1 : forall y, R (f1 _ y) (@t1 _ y))
  : match
      match t' as t0' in (@eq _ _ b0') return T (rta b0' t0') (rtb b0' t0') with
        | eq_refl => rt1 tt
      end
      as t0 in (@eq _ _ b0)
      return R b0 t0
    with
      | eq_refl => r1 tt
    end
    =
    match t'
          as t0' in (@eq _ _ b0')
          return (forall (R : forall (b : B (rta b0' t0')), T _ b -> Type)
                         (r1 : forall y, R (f1 _ y) (@t1 _ y)),
                    R _ (match t0' as t0'0 in (@eq _ _ b0'0) return T (rta b0'0 t0'0) (rtb b0'0 t0'0) with
                           | eq_refl => rt1 tt
                         end))
    with
      | eq_refl => fun _ r1 =>
                      match rt1 tt with
                        | eq_refl => r1 tt
                      end
    end R r1.
  Proof.
    destruct t'; reflexivity.
  Defined.

  Theorem eq_match_beta2
          a b (t : T a b)
          X
          (R : forall b' (t' : T a b'), X b' -> Type)
          (r1 : forall y x, R _ (@t1 _ y) x)
          x
  : match t as t' in (@eq _ _ b') return forall x, R b' t' x with
      | eq_refl => r1 tt
    end (x b)
    =
    match t as t' in (@eq _ _ b') return R b' t' (x b') with
      | eq_refl => r1 tt (x _)
    end.
  Proof.
    destruct t; reflexivity.
  Defined.
End eq.

Definition typeof {T} (_ : T) := T.

Eval compute in (eq_sym (eq_sym _)).
Goal forall T (x y : T) (p : x = y), True.
  intros.
  pose proof
       (@eq_matches_commute
          (existT (fun T => T) T x) y p
          (fun b'' _ => existT (fun T => T) T b'')
          (fun _ _ => x)
          (fun _ => eq_refl)
          (fun x' _ => x' = y)
          (fun _ => eq_refl)
        ) as H0.
  compute in H0.
  change (fun (x' : T) (_ : y = x') => x' = y) with ((fun y => fun (x' : T) (_ : y = x') => x' = y) y) in H0.
  Fail pose proof (fun k => @eq_trans _ _ _ k H0).
