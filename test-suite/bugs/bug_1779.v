Require Import Div2.

Lemma double_div2: forall n, div2 (double n) = n.
exact (fun n =>  let _subcase :=
    let _cofact := fun _ : 0 = 0 => refl_equal 0 in
    _cofact (let _fact := refl_equal 0 in _fact) in
  let _subcase0 :=
    fun (m : nat) (Hrec : div2 (double m) = m) =>
    let _fact := f_equal div2 (double_S m) in
    let _eq := trans_eq _fact (refl_equal (S (div2 (double m)))) in
    let _eq0 :=
      trans_eq _eq
        (trans_eq
           (f_equal (fun f : nat -> nat => f (div2 (double m)))
              (refl_equal S)) (f_equal S Hrec)) in
    _eq0 in
  (fix _fix (__ : nat) : div2 (double __) = __ :=
     match __ as n return (div2 (double n) = n) with
     | 0 => _subcase
     | S __0 =>
         (fun _hrec : div2 (double __0) = __0 => _subcase0 __0 _hrec)
           (_fix __0)
     end) n).
Guarded.
Defined.
