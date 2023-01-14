Inductive vector : nat -> Type :=
  | vector_Nil : vector 0
  | vector_Cons n : vector n -> vector (S n).

Fixpoint bv_and {n} (bv1 bv2 : vector n) : vector n :=
  match bv1 with
  | vector_Nil => fun _ => vector_Nil
  | vector_Cons n1' bv1' => fun bv2 =>
    match (bv2 : vector (S n1')) in (vector n2) return
      (match n2 with 0 => Type | S n2' => (vector n2' -> vector n1') -> vector (S n1') end) with
    | vector_Nil => Type
    | vector_Cons _ bv2' => fun cast => vector_Cons _ (bv_and bv1' (cast bv2'))
    end (fun x => x)
  end bv2.

Fixpoint bv_and2 {n} (bv1 bv2 : vector n) : vector n :=
  match bv1 with
  | vector_Nil => fun _ => vector_Nil
  | vector_Cons n1' bv1' => fun bv2 =>
    match (bv2 : vector (S n1')) in (vector n2) return
      (match n2 with 0 => Type | S n2' => (vector n2' -> vector n1') -> vector (S n1') end) with
    | vector_Nil => True -> True
    | vector_Cons _ bv2' => fun cast => vector_Cons _ (bv_and2 bv1' (cast bv2'))
    end (fun x => x)
  end bv2.
