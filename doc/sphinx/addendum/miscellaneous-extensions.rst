.. _miscellaneousextensions:

Miscellaneous extensions
========================

Program derivation
------------------

|Coq| comes with an extension called ``Derive``, which supports program
derivation. Typically in the style of Bird and Meertens or derivations
of program refinements. To use the Derive extension it must first be
required with ``Require Coq.derive.Derive``. When the extension is loaded,
it provides the following command:

.. cmd:: Derive @ident SuchThat @term As @ident

The first `ident` can appear in `term`. This command opens a new proof
presenting the user with a goal for term in which the name `ident` is
bound to an existential variable `?x` (formally, there are other goals
standing for the existential variables but they are shelved, as
described in :tacn:`shelve`).

When the proof ends two constants are defined:

+ The first one is named using the first `ident` and is defined as the proof of the
  shelved goal (which is also the value of `?x`). It is always
  transparent.
+ The second one is named using the second `ident`. It has type `term`, and its body is
  the proof of the initially visible goal. It is opaque if the proof
  ends with ``Qed``, and transparent if the proof ends with ``Defined``.

.. example::

  .. coqtop:: all

     Require Coq.derive.Derive.
     Require Import Coq.Numbers.Natural.Peano.NPeano.

     Section P.

     Variables (n m k:nat).

     Derive p SuchThat ((k*n)+(k*m) = p) As h.
     Proof.
     rewrite <- Nat.mul_add_distr_l.
     subst p.
     reflexivity.
     Qed.

     End P.

     Print p.
     Check h.

Any property can be used as `term`, not only an equation. In particular,
it could be an order relation specifying some form of program
refinement or a non-executable property from which deriving a program
is convenient.
