(* ZifyInt63 is deprecated as of Coq 8.14. Please use ZifyUint63 instead *)

Require Export ZifyUint63.

#[deprecated(since="8.14",note="Use ZifyUint63.to_Z_bounded instead.")]
Notation to_Z_bounded := to_Z_bounded (only parsing).

#[deprecated(since="8.14",note="Use ZifyUint63.ltb_lt instead.")]
Notation ltb_lt := ltb_lt (only parsing).

#[deprecated(since="8.14",note="Use ZifyUint63.leb_le instead.")]
Notation leb_le := leb_le (only parsing).

#[deprecated(since="8.14",note="Use ZifyUint63.eqb_eq instead.")]
Notation eqb_eq := eqb_eq (only parsing).

#[deprecated(since="8.14",note="Use ZifyUint63.eq_int_inj instead.")]
Notation eq_int_inj := eq_int_inj (only parsing).

#[deprecated(since="8.14",note="Use ZifyUint63.is_evenE instead.")]
Notation is_evenE := is_evenE (only parsing).
