Set Printing All.
Module NoDefinedAssoc.
  Reserved Notation "x $ y" (at level 123).
  Print Notation "x $ x".
  Axiom foo : Type.
  Axiom bar : forall _ : foo, forall _ : foo, foo.
  Notation "x $ y" := (bar x y) (only parsing).
  Check (_ $ _ $ _).
End NoDefinedAssoc.

Module NoAssoc.
  Reserved Notation "x $ y" (at level 123, no associativity).
  Print Notation "x $ x".
  Axiom foo : Type.
  Axiom bar : forall _ : foo, forall _ : foo, foo.
  Notation "x $ y" := (bar x y) (only parsing).
  Check (_ $ _ $ _).
End NoAssoc.

Module LeftAssoc.
  Reserved Notation "x $ y" (at level 123, left associativity).
  Print Notation "x $ x".
  Axiom foo : Type.
  Axiom bar : forall _ : foo, forall _ : foo, foo.
  Notation "x $ y" := (bar x y) (only parsing).
  Check (_ $ _ $ _).
End LeftAssoc.

Module RightAssoc.
  Reserved Notation "x $ y" (at level 123, right associativity).
  Print Notation "x $ x".
  Axiom foo : Type.
  Axiom bar : forall _ : foo, forall _ : foo, foo.
  Notation "x $ y" := (bar x y) (only parsing).
  Check (_ $ _ $ _).
  Fail Print Notation "_ $ x".
  Fail Print Notation "_ $".
  Fail Print Notation "$ x".
  Fail Print Notation "x$y".
  Fail Print Notation "_$_".
  Print Notation "y $ x".
  Print Notation "_ $ _".
End RightAssoc.

(** Stdlib notations *)
Module StdlibNotations.
  Import IfNotations.
  Print Notation "x -> y".
  Print Notation "x <-> y".
  Print Notation "x /\ y".
  Print Notation "x \/ y".
  Print Notation "~ x".
  Print Notation "x = y  :>  T".
  Print Notation "x = y".
  Print Notation "x = y = z".
  Print Notation "x <> y  :>  T".
  Print Notation "x <> y".
  Print Notation "x <= y".
  Print Notation "x < y".
  Print Notation "x >= y".
  Print Notation "x > y".
  Print Notation "x <= y <= z".
  Print Notation "x <= y < z".
  Print Notation "x < y < z".
  Print Notation "x < y <= z".
  Print Notation "x + y".
  Print Notation "x - y".
  Print Notation "x * y".
  Print Notation "x / y".
  Print Notation "- x".
  Print Notation "/ x".
  Print Notation "x ^ y".
  Print Notation "x || y".
  Print Notation "x && y".
  Print Notation "( x , y , .. , z )".
  Print Notation "{ x }".
  Print Notation "{ A }  +  { B }".
  Print Notation "A  +  { B }".
  Print Notation "{ x | P }".
  Print Notation "{ x | P & Q }".
  Print Notation "{ x : A | P }".
  Print Notation "{ x : A | P & Q }".
  Print Notation "{ x & P }".
  Print Notation "{ x & P & Q }".
  Print Notation "{ x : A & P }".
  Print Notation "{ x : A & P & Q }".
  Print Notation "{ ' pat | P }".
  Print Notation "{ ' pat | P & Q }".
  Print Notation "{ ' pat : A | P }".
  Print Notation "{ ' pat : A | P & Q }".
  Print Notation "{ ' pat & P }".
  Print Notation "{ ' pat & P & Q }".
  Print Notation "{ ' pat : A & P }".
  Print Notation "{ ' pat : A & P & Q }".
  Print Notation "'if' c 'is' p 'then' u 'else' v".
End StdlibNotations.

Module StdlibNotationsUnderscored.
  Import IfNotations.
  Print Notation "_ -> _".
  Print Notation "_ <-> _".
  Print Notation "_ /\ _".
  Print Notation "_ \/ _".
  Print Notation "~ _".
  Print Notation "_ = _  :> _".
  Print Notation "_ = _".
  Print Notation "_ = _ = _".
  Print Notation "_ <> _  :> _".
  Print Notation "_ <> _".
  Print Notation "_ <= _".
  Print Notation "_ < _".
  Print Notation "_ >= _".
  Print Notation "_ > _".
  Print Notation "_ <= _ <= _".
  Print Notation "_ <= _ < _".
  Print Notation "_ < _ < _".
  Print Notation "_ < _ <= _".
  Print Notation "_ + _".
  Print Notation "_ - _".
  Print Notation "_ * _".
  Print Notation "_ / _".
  Print Notation "- _".
  Print Notation "/ _".
  Print Notation "_ ^ _".
  Print Notation "_ || _".
  Print Notation "_ && _".
  Print Notation "( _ , _ , .. , _ )".
  Print Notation "{ _ }".
  Print Notation "{ _ }  +  { _ }".
  Print Notation "_  +  { _ }".
  Print Notation "{ _ | _ }".
  Print Notation "{ _ | _ & _ }".
  Print Notation "{ _ : _ | _ }".
  Print Notation "{ _ : _ | _ & _ }".
  Print Notation "{ _ & _ }".
  Print Notation "{ _ & _ & _ }".
  Print Notation "{ _ : _ & _ }".
  Print Notation "{ _ : _ & _ & _ }".
  Print Notation "{ ' _ | _ }".
  Print Notation "{ ' _ | _ & _ }".
  Print Notation "{ ' _ : _ | _ }".
  Print Notation "{ ' _ : _ | _ & _ }".
  Print Notation "{ ' _ & _ }".
  Print Notation "{ ' _ & _ & _ }".
  Print Notation "{ ' _ : _ & _ }".
  Print Notation "{ ' _ : _ & _ & _ }".
  Print Notation "if _ is _ then _ else _".
End StdlibNotationsUnderscored.

(* Print Notatation doesn't work with custom notations *)
Module Custom.
  Declare Custom Entry Foo.
  Reserved Notation "{{ x }}" (in custom Foo at level 0).
  Print Notation "{{ x }}" in custom Foo.
  Print Notation "{{ _ }}" in custom Foo.
  Fail Print Notation "{{ x }}" in custom Bar.
  Fail Print Notation "{{ _ }}" in custom Bar.
  Fail Print Notation "[[ x ]]" in custom Foo.
  Fail Print Notation "[[ _ ]]" in custom Foo.
End Custom.

Module OnlyLetters.
  Reserved Infix "mod" (at level 40, no associativity).
  Fail Print Notation "x mod y".
  Print Notation "x 'mod' y".
  Print Notation "_ mod _".
  Print Notation "_ 'mod' _".
  Axiom foo : Type.
  Axiom bar : forall _ : foo, forall _ : foo, foo.
  Infix "mod" := bar (only parsing).
  Check (_ mod _ mod _).
End OnlyLetters.

Module SingleQuotes.
  Reserved Infix "'mod'" (at level 40, no associativity).
  Fail Print Notation "x 'mod' y".
  Print Notation "x ''mod'' y".
  Fail Print Notation "_ 'mod' _". (* FIXME I expected this to work *)
  Print Notation "_ ''mod'' _".
  Axiom foo : Type.
  Axiom bar : forall _ : foo, forall _ : foo, foo.
  Infix "'mod'" := bar (only parsing).
  Check (_ 'mod' _ 'mod' _).
End SingleQuotes.

Module Recursive.
  Reserved Notation "'exists' x .. y , p"
    (at level 200, x binder, right associativity,
    format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'").
  Fail Print Notation "exists x .. y , p".
  Print Notation "'exists' x .. y , p".
  Print Notation "exists _ .. _ , _".
  Fail Print Notation "exists _ , _".
  Fail Print Notation "exists _ _ , _".
End Recursive.
