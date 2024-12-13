The standard library
--------------------

Survey
~~~~~~

The standard library is structured into the following
subdirectories:

  * **Logic** : Classical logic and dependent equality
  * **Arith** : Basic Peano arithmetic
  * **PArith** : Basic positive integer arithmetic
  * **NArith** : Basic binary natural number arithmetic
  * **ZArith** : Basic relative integer arithmetic
  * **Numbers** : Various approaches to natural, integer and cyclic numbers (currently axiomatically and on top of 2^31 binary words)
  * **Bool** : Booleans (basic functions and results)
  * **Lists** : Monomorphic and polymorphic lists (basic functions and results), Streams (infinite sequences defined with coinductive types)
  * **Sets** : Sets (classical, constructive, finite, infinite, power set, etc.)
  * **FSets** : Specification and implementations of finite sets and finite maps (by lists and by AVL trees)
  * **Reals** : Axiomatization of real numbers (classical, basic functions, integer part, fractional part, limit, derivative, Cauchy series, power series and results,...)
  * **Floats** : Machine implementation of floating-point arithmetic (for the binary64 format)
  * **Relations** : Relations (definitions and basic results)
  * **Sorting** : Sorted list (basic definitions and heapsort correctness)
  * **Strings** : 8-bits characters and strings
  * **Wellfounded** : Well-founded relations (basic results)


These directories belong to the initial load path of the system, and
the modules they provide are compiled at installation time. So they
are directly accessible with the command ``Require``.

The different modules of the Coq standard library are documented
online at https://coq.inria.fr/stdlib/.

Peano’s arithmetic (nat)
~~~~~~~~~~~~~~~~~~~~~~~~

.. index::
   single: Peano's arithmetic
   single: nat_scope

While in the initial state, many operations and predicates of Peano's
arithmetic are defined, further operations and results belong to other
modules. For instance, the decidability of the basic predicates are
defined here. This is provided by requiring the module ``Arith``.

The following table describes the notations available in scope
``nat_scope`` :

===============   ===================
Notation          Interpretation
===============   ===================
``_ < _``         ``lt``
``_ <= _``        ``le``
``_ > _``         ``gt``
``_ >= _``        ``ge``
``x < y < z``     ``x < y /\ y < z``
``x < y <= z``    ``x < y /\ y <= z``
``x <= y < z``    ``x <= y /\ y < z``
``x <= y <= z``   ``x <= y /\ y <= z``
``_ + _``         ``plus``
``_ - _``         ``minus``
``_ * _``         ``mult``
===============   ===================


Notations for integer arithmetic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. index::
  single: Arithmetical notations
  single: + (term)
  single: * (term)
  single: - (term)
  singel: / (term)
  single: <= (term)
  single: >= (term)
  single: < (term)
  single: > (term)
  single: ?= (term)
  single: mod (term)


The following table describes the syntax of expressions
for integer arithmetic. It is provided by requiring and opening the module ``ZArith`` and opening scope ``Z_scope``.
It specifies how notations are interpreted and, when not
already reserved, the precedence and associativity.

===============   ====================  ==========  =============
Notation          Interpretation        Precedence  Associativity
===============   ====================  ==========  =============
``_ < _``         ``Z.lt``
``_ <= _``        ``Z.le``
``_ > _``         ``Z.gt``
``_ >= _``        ``Z.ge``
``x < y < z``     ``x < y /\ y < z``
``x < y <= z``    ``x < y /\ y <= z``
``x <= y < z``    ``x <= y /\ y < z``
``x <= y <= z``   ``x <= y /\ y <= z``
``_ ?= _``        ``Z.compare``         70          no
``_ + _``         ``Z.add``
``_ - _``         ``Z.sub``
``_ * _``         ``Z.mul``
``_ / _``         ``Z.div``
``_ mod _``       ``Z.modulo``          40          no
``- _``           ``Z.opp``
``_ ^ _``         ``Z.pow``
===============   ====================  ==========  =============


.. example::

  .. rocqtop:: all reset

    From Stdlib Require Import ZArith.
    Check (2 + 3)%Z.
    Open Scope Z_scope.
    Check 2 + 3.


Real numbers library
~~~~~~~~~~~~~~~~~~~~

Notations for real numbers
++++++++++++++++++++++++++

This is provided by requiring and opening the module ``Reals`` and
opening scope ``R_scope``. This set of notations is very similar to
the notation for integer arithmetic. The inverse function was added.

===============   ===================
Notation          Interpretation
===============   ===================
``_ < _``         ``Rlt``
``_ <= _``        ``Rle``
``_ > _``         ``Rgt``
``_ >= _``        ``Rge``
``x < y < z``     ``x < y /\ y < z``
``x < y <= z``    ``x < y /\ y <= z``
``x <= y < z``    ``x <= y /\ y < z``
``x <= y <= z``   ``x <= y /\ y <= z``
``_ + _``         ``Rplus``
``_ - _``         ``Rminus``
``_ * _``         ``Rmult``
``_ / _``         ``Rdiv``
``- _``           ``Ropp``
``/ _``           ``Rinv``
``_ ^ _``         ``pow``
===============   ===================

.. example::

  .. rocqtop:: all reset

    From Stdlib Require Import Reals.
    Check  (2 + 3)%R.
    Open Scope R_scope.
    Check 2 + 3.

Some tactics for real numbers
+++++++++++++++++++++++++++++

In addition to the powerful ``ring``, ``field`` and ``lra``
tactics (see Chapters ring and micromega), there are also:

.. tacn:: discrR

  Proves that two real integer constants are different.

.. example::

  .. rocqtop:: all reset

    From Stdlib Require Import DiscrR.
    Open Scope R_scope.
    Goal 5 <> 0.
    discrR.

.. tacn:: split_Rabs

  Allows unfolding the ``Rabs`` constant and splits corresponding conjunctions.

.. example::

  .. rocqtop:: all reset

    From Stdlib Require Import Reals.
    Open Scope R_scope.
    Goal forall x:R, x <= Rabs x.
    intro; split_Rabs.

.. tacn:: split_Rmult

  Splits a condition that a product is non-null into subgoals
  corresponding to the condition on each operand of the product.

.. example::

  .. rocqtop:: all reset

    From Stdlib Require Import Reals.
    Open Scope R_scope.
    Goal forall x y z:R, x * y * z <> 0.
    intros; split_Rmult.

List library
~~~~~~~~~~~~

.. index::
  single: Notations for lists
  single: length (term)
  single: head (term)
  single: tail (term)
  single: app (term)
  single: rev (term)
  single: nth (term)
  single: map (term)
  single: flat_map (term)
  single: fold_left (term)
  single: fold_right (term)

Some elementary operations on polymorphic lists are defined here.
They can be accessed by requiring module ``List``.

It defines the following notions:

  * ``length``
  * ``head`` : first element (with default)
  * ``tail`` : all but first element
  * ``app`` : concatenation
  * ``rev`` : reverse
  * ``nth`` : accessing n-th element (with default)
  * ``map`` : applying a function
  * ``flat_map`` : applying a function returning lists
  * ``fold_left`` : iterator (from head to tail)
  * ``fold_right`` : iterator (from tail to head)

The following table shows notations available when opening scope ``list_scope``.

==========  ==============  ==========  =============
Notation    Interpretation  Precedence  Associativity
==========  ==============  ==========  =============
``_ ++ _``  ``app``         60          right
``_ :: _``  ``cons``        60          right
==========  ==============  ==========  =============

.. _floats_library:

Floats library
~~~~~~~~~~~~~~

The standard library has a small ``Floats`` module for accessing
processor floating-point operations through the Coq kernel.
However, while this module supports computation and has a bit-level
specification, it doesn't include elaborate theorems, such as a link
to real arithmetic or various error bounds. To do proofs by
reflection, use ``Floats`` in conjunction with the complementary
`Flocq <https://flocq.gitlabpages.inria.fr/>`_ library, which provides
many such theorems.

The library of primitive floating-point arithmetic can be loaded by
requiring module ``Floats``:

.. rocqtop:: in

  From Stdlib Require Import Floats.

It exports the module ``PrimFloat`` that provides a primitive type
named ``float``, defined in the kernel
as well as two variant types ``float_comparison`` and ``float_class``:


.. rocqtop:: all

  Print float.
  Print float_comparison.
  Print float_class.

It then defines the primitive operators below, using the processor
floating-point operators for binary64 in rounding-to-nearest even:

* ``abs``
* ``opp``
* ``sub``
* ``add``
* ``mul``
* ``div``
* ``sqrt``
* ``compare`` : compare two floats and return a ``float_comparison``
* ``classify`` : analyze a float and return a ``float_class``
* ``of_int63`` : round a primitive integer and convert it into a float
* ``normfr_mantissa`` : take a float in ``[0.5; 1.0)`` and return its mantissa
* ``frshiftexp`` : convert a float to fractional part in ``[0.5; 1.0)`` and integer part
* ``ldshiftexp`` : multiply a float by an integral power of ``2``
* ``next_up`` : return the next float towards positive infinity
* ``next_down`` : return the next float towards negative infinity

For special floating-point values, the following constants are also
defined:

* ``zero``
* ``neg_zero``
* ``one``
* ``two``
* ``infinity``
* ``neg_infinity``
* ``nan`` : Not a Number (assumed to be unique: the "payload" of NaNs is ignored)

The following table shows the notations available when opening scope
``float_scope``.

===========  ==============
Notation     Interpretation
===========  ==============
``- _``      ``opp``
``_ - _``    ``sub``
``_ + _``    ``add``
``_ * _``    ``mul``
``_ / _``    ``div``
``_ =? _``   ``eqb``
``_ <? _``    ``ltb``
``_ <=? _``   ``leb``
``_ ?= _``   ``compare``
===========  ==============

Floating-point constants are parsed and pretty-printed as (17-digit)
decimal constants. This ensures that the composition
:math:`\text{parse} \circ \text{print}` amounts to the identity.

.. warn:: The constant number is not a binary64 floating-point value.  A closest value number will be used and unambiguously printed number. [inexact-float,parsing]

   Not all decimal constants are floating-point values. This warning
   is generated when parsing such a constant (for instance ``0.1``).

.. flag:: Printing Float

   Turn this flag off (it is on by default) to deactivate decimal
   printing of floating-point constants. They will then be printed
   with an hexadecimal representation.

.. example::

  .. rocqtop:: all

    Open Scope float_scope.
    Eval compute in 1 + 0.5.
    Eval compute in 1 / 0.
    Eval compute in 1 / -0.
    Eval compute in 0 / 0.
    Eval compute in 0 ?= -0.
    Eval compute in nan ?= nan.
    Eval compute in next_down (-1).

The primitive operators are specified with respect to their Gallina
counterpart, using the variant type ``spec_float``, and the injection
``Prim2SF``:

.. rocqtop:: all

  Print spec_float.
  Check Prim2SF.
  Check mul_spec.

For more details on the available definitions and lemmas, see the
online documentation of the ``Floats`` library.

.. _pstring_library:

Primitive strings library
~~~~~~~~~~~~~~~~~~~~~~~~~

The standard library provides a ``PrimString`` module declaring a primitive
string type ``PrimString.string`` (corresponding to the OCaml ``string`` type),
together with a small set of primitive functions:

* ``max_length`` : gives the maximum length of a string
* ``make`` : builds a string of the given length conly containing the given byte
* ``length`` : gives the lenght of the given string
* ``get`` : gives the byte at a given index in the given string
* ``sub`` : extracts the sub-string from the given string that starts at the given offset and with the given length
* ``cat`` : concatenates the two given strings
* ``compare`` : compares the two strings and returns a ``comparison``

Bytes are represented using the ``PrimString.char63``, which is defined as ``Uint63.int``,
but primitive strings only store values fitting on 8 bits (i.e., values between 0 and 255).

Axiomatic specifications of these primitive string functions are provided in the
``PrimStringAxioms`` module. Additional properties, and relations to equivalent
primitives defined in Gallina are provided in module ``PString`` (which exports
``PrimString`` and ``PrimStringAxioms``.

A custom string notation is provided for the ``string`` and ``char63`` types,
in respective scopes ``pstring`` and ``char63``.
