Primitive objects
=================

.. _primitive-integers:

Primitive Integers
------------------

The language of terms features 63-bit machine integers as values. The type of
such a value is *axiomatized*; it is declared through the following sentence
(excerpt from the :g:`Int63` module):

.. coqdoc::

   Primitive int := #int63_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, equality of two primitive integers can be decided using the :g:`Int63.eqb` function,
declared and specified as follows:

.. coqdoc::

   Primitive eqb := #int63_eq.
   Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

   Axiom eqb_correct : forall i j, (i == j)%int63 = true -> i = j.

The complete set of such operators can be obtained looking at the :g:`Int63` module.

These primitive declarations are regular axioms. As such, they must be trusted and are listed by the
:g:`Print Assumptions` command, as in the following example.

.. coqtop:: in reset

   From Coq Require Import Int63.
   Lemma one_minus_one_is_zero : (1 - 1 = 0)%int63.
   Proof. apply eqb_correct; vm_compute; reflexivity. Qed.

.. coqtop:: all

   Print Assumptions one_minus_one_is_zero.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient, rules to reduce the applications of these primitive
operations.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlInt63`
module can be used when extracting to OCaml: it maps the Coq primitives to types
and functions of a :g:`Uint63` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Coq.

Literal values (at type :g:`Int63.int`) are extracted to literal OCaml values
wrapped into the :g:`Uint63.of_int` (resp. :g:`Uint63.of_int64`) constructor on
64-bit (resp. 32-bit) platforms. Currently, this cannot be customized (see the
function :g:`Uint63.compile` from the kernel).

.. _primitive-floats:

Primitive Floats
----------------

The language of terms features Binary64 floating-point numbers as values.
The type of such a value is *axiomatized*; it is declared through the
following sentence (excerpt from the :g:`PrimFloat` module):

.. coqdoc::

   Primitive float := #float64_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, the product of two primitive floats can be computed using the
:g:`PrimFloat.mul` function, declared and specified as follows:

.. coqdoc::

   Primitive mul := #float64_mul.
   Notation "x * y" := (mul x y) : float_scope.

   Axiom mul_spec : forall x y, Prim2SF (x * y)%float = SF64mul (Prim2SF x) (Prim2SF y).

where :g:`Prim2SF` is defined in the :g:`FloatOps` module.

The set of such operators is described in section :ref:`floats_library`.

These primitive declarations are regular axioms. As such, they must be trusted, and are listed by the
:g:`Print Assumptions` command.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient rules to reduce the applications of these primitive
operations, using the floating-point processor operators that are assumed
to comply with the IEEE 754 standard for floating-point arithmetic.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlFloats`
module can be used when extracting to OCaml: it maps the Coq primitives to types
and functions of a :g:`Float64` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Coq.

Literal values (of type :g:`Float64.t`) are extracted to literal OCaml
values (of type :g:`float`) written in hexadecimal notation and
wrapped into the :g:`Float64.of_float` constructor, e.g.:
:g:`Float64.of_float (0x1p+0)`.
