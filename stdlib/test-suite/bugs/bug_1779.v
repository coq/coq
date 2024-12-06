From Stdlib Require Import PeanoNat.

Lemma double_div2: forall n, Nat.div2 (Nat.double n) = n.
exact (fun n =>  let _subcase :=
    let _cofact := fun _ : 0 = 0 => refl_equal 0 in
    _cofact (let _fact := refl_equal 0 in _fact) in
  let _subcase0 :=
    fun (m : nat) (Hrec : Nat.div2 (Nat.double m) = m) =>
    let _fact := f_equal Nat.div2 (Nat.double_S m) in
    let _eq := trans_eq _fact (refl_equal (S (Nat.div2 (Nat.double m)))) in
    let _eq0 :=
      trans_eq _eq
        (trans_eq
           (f_equal (fun f : nat -> nat => f (Nat.div2 (Nat.double m)))
              (refl_equal S)) (f_equal S Hrec)) in
    _eq0 in
  (fix _fix (__ : nat) : Nat.div2 (Nat.double __) = __ :=
     match __ as n return (Nat.div2 (Nat.double n) = n) with
     | 0 => _subcase
     | S __0 =>
         (fun _hrec : Nat.div2 (Nat.double __0) = __0 => _subcase0 __0 _hrec)
           (_fix __0)
     end) n).
Guarded.
Defined.
