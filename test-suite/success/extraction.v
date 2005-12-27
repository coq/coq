(* Mini extraction test *)

Require Import ZArith.

Extraction "zarith.ml" two_or_two_plus_one Zdiv_eucl_exist.
