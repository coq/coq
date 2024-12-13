Primitive objects
=================

.. _primitive-integers:

Primitive Integers
------------------

The language of terms features 63-bit machine integers as values. The type of
such a value is *axiomatized*; it is declared through the following sentence
(excerpt from the :g:`PrimInt63` module):

.. rocqdoc::

   Primitive int := #int63_type.

This type can be understood as representing either unsigned or signed integers,
depending on which module is imported or, more generally, which scope is open.
:g:`Uint63` and :g:`uint63_scope` refer to the unsigned version, while :g:`Sint63`
and :g:`sint63_scope` refer to the signed one.

The :g:`PrimInt63` module declares the available operators for this type.
For instance, equality of two unsigned primitive integers can be determined using
the :g:`Uint63.eqb` function, declared and specified as follows:

.. rocqdoc::

   Primitive eqb := #int63_eq.
   Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : uint63_scope.

   Axiom eqb_correct : forall i j, (i == j)%uint63 = true -> i = j.

The complete set of such operators can be found in the :g:`PrimInt63` module.
The specifications and notations are in the :g:`Uint63` and :g:`Sint63`
modules.

These primitive declarations are regular axioms. As such, they must be trusted and are listed by the
:g:`Print Assumptions` command, as in the following example.

.. rocqtop:: in reset

   From Corelib Require Import PrimInt63 Uint63Axioms.
   Lemma one_minus_one_is_zero : (sub 1 1 = 0)%uint63.
   Proof. apply eqb_correct; vm_compute; reflexivity. Qed.

.. rocqtop:: all

   Print Assumptions one_minus_one_is_zero.

The reduction machines implement dedicated, efficient rules to reduce the
applications of these primitive operations.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlInt63`
module can be used when extracting to OCaml: it maps the Rocq primitives to types
and functions of a :g:`Uint63` module (including signed functions for
:g:`Sint63` despite the name). That OCaml module is not produced by extraction.
Instead, it has to be provided by the user (if they want to compile or execute
the extracted code). For instance, an implementation of this module can be taken
from the kernel of Rocq.

Literal values (at type :g:`Uint63.int`) are extracted to literal OCaml values
wrapped into the :g:`Uint63.of_int` (resp. :g:`Uint63.of_int64`) constructor on
64-bit (resp. 32-bit) platforms. Currently, this cannot be customized (see the
function :g:`Uint63.compile` from the kernel).

.. _primitive-floats:

Primitive Floats
----------------

The language of terms features Binary64 floating-point numbers as values.
The type of such a value is *axiomatized*; it is declared through the
following sentence (excerpt from the :g:`PrimFloat` module):

.. rocqdoc::

   Primitive float := #float64_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, the product of two primitive floats can be computed using the
:g:`PrimFloat.mul` function, declared and specified as follows:

.. rocqdoc::

   Primitive mul := #float64_mul.
   Notation "x * y" := (mul x y) : float_scope.

   Axiom mul_spec : forall x y, Prim2SF (x * y)%float = SF64mul (Prim2SF x) (Prim2SF y).

where :g:`Prim2SF` is defined in the :g:`FloatOps` module.

These primitive declarations are regular axioms. As such, they must be trusted, and are listed by the
:g:`Print Assumptions` command.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient rules to reduce the applications of these primitive
operations, using the floating-point processor operators that are assumed
to comply with the IEEE 754 standard for floating-point arithmetic.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlFloats`
module can be used when extracting to OCaml: it maps the Rocq primitives to types
and functions of a :g:`Float64` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Rocq.

Literal values (of type :g:`Float64.t`) are extracted to literal OCaml
values (of type :g:`float`) written in hexadecimal notation and
wrapped into the :g:`Float64.of_float` constructor, e.g.:
:g:`Float64.of_float (0x1p+0)`.

.. _primitive-arrays:

Primitive Arrays
----------------

The language of terms features persistent arrays as values. The type of
such a value is *axiomatized*; it is declared through the following sentence
(excerpt from the :g:`PArray` module):

.. rocqdoc::

   Primitive array := #array_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, elements in an array can be accessed and updated using the
:g:`PArray.get` and :g:`PArray.set` functions, declared and specified as
follows:

.. rocqdoc::

   Primitive get := #array_get.
   Primitive set := #array_set.
   Notation "t .[ i ]" := (get t i).
   Notation "t .[ i <- a ]" := (set t i a).

   Axiom get_set_same : forall A t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a.
   Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].

The rest of these operators can be found in the :g:`PArray` module.

These primitive declarations are regular axioms. As such, they must be trusted and are listed by the
:g:`Print Assumptions` command.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient rules to reduce the applications of these primitive
operations.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlPArray`
module can be used when extracting to OCaml: it maps the Rocq primitives to types
and functions of a :g:`Parray` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Rocq (see ``kernel/parray.ml``).

Rocq's primitive arrays are persistent data structures. Semantically, a set operation
``t.[i <- a]`` represents a new array that has the same values as ``t``, except
at position ``i`` where its value is ``a``. The array ``t`` still exists, can
still be used and its values were not modified. Operationally, the implementation
of Rocq's primitive arrays is optimized so that the new array ``t.[i <- a]`` does not
copy all of ``t``. The details are in section 2.3 of :cite:`ConchonFilliatre07wml`.
In short, the implementation keeps one version of ``t`` as an OCaml native array and
other versions as lists of modifications to ``t``. Accesses to the native array
version are constant time operations. However, accesses to versions where all the cells of
the array are modified have O(n) access time, the same as a list. The version that is kept as the native array
changes dynamically upon each get and set call: the current list of modifications
is applied to the native array and the lists of modifications of the other versions
are updated so that they still represent the same values.

.. _primitive-string:

Primitive (Byte-Based) Strings
------------------------------

The language of terms supports immutable strings as values. Primitive strings
are *axiomatized*.  The type is declared through the following sentence (excerpt
from the :g:`PrimString` module):

.. rocqdoc::

   Primitive string := #string_type.

This type is equipped with functions that must be similarly declared. For example,
the length of a string can be computed with :g:`PrimString.length`, and the character
(i.e., byte) at a given position can be obtained with :g:`PrimString.get`. These
functions are defined as follows:

.. rocqdoc::

   Definition char63 := int.

   Primitive length : string -> int := #string_length.
   Primitive get : string -> int -> char63 := #string_get.

The remaining primitives can be found in the :g:`PrimString` module.

These primitive declarations are regular axioms. As such, they must be trusted and
are listed by the :g:`Print Assumptions` command.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient rules to reduce the applications of these primitive
operations.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlPString`
module can be used when extracting to OCaml: it maps the Rocq primitives to types
and functions of a :g:`Pstring` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Rocq (see ``kernel/pstring.ml``).

Literal values (of type :g:`Pstring.t`, or equivalently :g:`string`) are extracted
to literal OCaml values (of type :g:`string`).
