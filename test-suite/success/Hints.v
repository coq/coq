(* Checks syntax of Hints commands *)
(* Checks that qualified names are accepted *)

(* New-style syntax *)
Hint h1 : core arith := Resolve Logic.refl_equal.
Hint h2 := Immediate Logic.trans_equal.
Hint h3 : core := Unfold Logic.sym_equal.
Hint h4 : foo bar := Constructors Logic.eq.
Hint h5 : foo bar := Extern 3 (eq ? ? ?) Apply Logic.refl_equal.

(* Old-style syntax *)
Hints Resolve Coq.Init.Logic.refl_equal Coq.Init.Logic.sym_equal.
Hints Resolve Coq.Init.Logic.refl_equal Coq.Init.Logic.sym_equal : foo.
Hints Immediate Coq.Init.Logic.refl_equal Coq.Init.Logic.sym_equal.
Hints Immediate Coq.Init.Logic.refl_equal Coq.Init.Logic.sym_equal : foo.
Hints Unfold Coq.Init.Datatypes.fst Coq.Init.Logic.sym_equal.
Hints Unfold Coq.Init.Datatypes.fst Coq.Init.Logic.sym_equal : foo.

(* What's this stranged syntax ? *)
HintDestruct Conclusion h6 (le ? ?) 4 [ Fun H -> Apply H ].
HintDestruct Discardable Hypothesis h7 (le ? ?) 4 [ Fun H -> Apply H ].
HintDestruct Hypothesis h8 (le ? ?) 4 [ Fun H -> Apply H ].

(* Checks that local names are accepted *)
Section A.
  Remark Refl : (A:Set)(x:A)x=x. 
  Proof refl_equal.
  Definition Sym := sym_equal.
  Local Trans := trans_equal.
 
  Hint h1 : foo := Resolve Refl.
  Hint h2 : bar := Resolve Sym.
  Hint h3 : foo2 := Resolve Trans.

  Hint h2 := Immediate Refl.
  Hint h2 := Immediate Sym.
  Hint h2 := Immediate Trans.

  Hint h3 := Unfold Refl.
  Hint h3 := Unfold Sym.
  Hint h3 := Unfold Trans.

  Hints Resolve Sym Trans Refl.
  Hints Immediate Sym Trans Refl.
  Hints Unfold Sym Trans Refl.

End A.

