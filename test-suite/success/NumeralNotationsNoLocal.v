(* Test that numeral notations don't work on proof-local variables, especially not ones containing evars *)
Inductive unit11 := tt11.
Declare Scope unit11_scope.
Delimit Scope unit11_scope with unit11.
Goal True.
  evar (to_uint : unit11 -> Decimal.uint).
  evar (of_uint : Decimal.uint -> unit11).
  Fail Numeral Notation unit11 of_uint to_uint : uint11_scope.
  exact I.
  Unshelve.
  all: solve [ constructor ].
Qed.
