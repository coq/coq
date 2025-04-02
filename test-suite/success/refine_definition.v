
#[refine] Definition test : { x : nat | x < 4 } := exist _ 3 _.
Proof.
  constructor.
Defined.

#[refine] Fixpoint fixtest (n : nat) :=
  match n with
  | 0 => _
  | S k => _
  end.
Proof.
  1: shelve.
  - exact 1.
  - refine (n * _).
    apply fixtest.
    apply k.
Defined.


#[refine] Definition infer_test := 1 + _.
Proof.
  apply fixtest, 1.
Qed.

#[refine] Definition true_infer_test := _.
Proof.
  2: exact (if true as b return if b then _ else _ then 0 else false).
Qed.

(* Cannot use Eval with #[refine]. *)
Fail #[refine] Definition notest := Eval lazy in 0 + 0.
