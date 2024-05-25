Program derivation
==================

Coq comes with an extension called ``Derive``, which supports program
derivation. Typically in the style of Bird and Meertens or derivations
of program refinements. To use the Derive extension it must first be
required with ``Require Coq.derive.Derive``. When the extension is loaded,
it provides the following command:

.. cmd:: Derive @ident__1 {? : @type__1 } SuchThat @type__2 As @ident__2

   :n:`@ident__1` can appear in :n:`@type__2`. This command opens a new proof
   presenting the user with a goal for :n:`@type__2` in which the name :n:`@ident__1` is
   bound to an existential variable :g:`?x` (formally, there are other goals
   standing for the existential variables but they are shelved, as
   described in :tacn:`shelve`). A specific type :n:`@type__1` can
   optionally be given to :n:`@ident__1`.

   When the proof ends two :term:`constants <constant>` are defined:

   + The first one is named :n:`@ident__1` and is defined as the proof of the
     shelved goal (which is also the value of :g:`?x`). It is always
     transparent.
   + The second one is named :n:`@ident__2`. It has type :n:`@type`, and its :term:`body` is
     the proof of the initially visible goal. It is opaque if the proof
     ends with :cmd:`Qed`, and transparent if the proof ends with :cmd:`Defined`.

.. example::

  .. coqtop:: all

     Require Coq.derive.Derive.
     Require Import PeanoNat.

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
