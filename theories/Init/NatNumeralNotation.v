Require Coq.Init.Datatypes.
Require Coq.Init.Nat.

Declare ML Module "numeral_notation_plugin".

(* Parsing / printing of decimal numbers *)
Arguments Nat.of_uint d%dec_uint_scope.
Arguments Nat.of_int d%dec_int_scope.
Numeral Notation Decimal.uint Decimal.uint_of_uint Decimal.uint_of_uint
  : dec_uint_scope.
Numeral Notation Decimal.int Decimal.int_of_int Decimal.int_of_int
  : dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Numeral Notation Datatypes.nat Nat.of_uint Nat.to_uint : nat_scope (abstract after 5000).
