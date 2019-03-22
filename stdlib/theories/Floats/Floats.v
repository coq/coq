(** The Floats library is split in 6 theories:
- FloatClass: define the [float_class] inductive
- PrimFloat: define the floating-point values and operators as kernel primitives
- SpecFloat: specify the floating-point operators with binary integers
- FloatOps: define conversion functions between [spec_float] and [float]
- FloatAxioms: state properties of the primitive operators w.r.t. [spec_float]
- FloatLemmas: prove a few results involving frexp and ldexp

For a brief overview of the Floats library,
see {{https://coq.inria.fr/distrib/current/refman/language/coq-library.html#floats-library}} *)

Require Export FloatClass.
Require Export PrimFloat.
Require Export SpecFloat.
Require Export FloatOps.
Require Export FloatAxioms.
Require Export FloatLemmas.
