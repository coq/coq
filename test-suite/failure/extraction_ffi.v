From Corelib Require NatDef.
From Corelib Require Extraction.

(* Define axiomatic functions. *)
Axiom ax_fun : nat -> nat.
Axiom ax_fun2 : nat -> nat.

(* Declare a function that executes ax_fun if a is positive
    and returns 0, else. *)
Definition my_fun (a : nat) :=
  if Nat.leb a 0
  then ax_fun a
  else 0.

(* Extraction of foreign constant and callback for Haskell must fail *)
Extraction Language Haskell.
Fail Extract Foreign Constant ax_fun => "my_c_fun".
Fail Extract Callback "call_my_fun" my_fun.

(* Extraction of foreign constant and callback for Scheme must fail *)
Extraction Language Scheme.
Fail Extract Foreign Constant ax_fun => "my_c_fun".
Fail Extract Callback "call_my_fun" my_fun.

(* Extraction of foreign constant and callback for JSON must fail *)
Extraction Language JSON.
Fail Extract Foreign Constant ax_fun => "my_c_fun".
Fail Extract Callback "call_my_fun" my_fun.

(* Extraction of foreign constant for already defined inlined ml function must fail. *)
Extraction Language OCaml.
Extract Inlined Constant ax_fun => "my_ml_fun".
Fail Extract Foreign Constant ax_fun => "my_c_fun".

(* Extraction of inlined constant for already defined foreign function must fail. *)
Extract Foreign Constant ax_fun2 => "my_c_fun".
Fail Extract Inlined Constant ax_fun2 => "my_ml_fun".
