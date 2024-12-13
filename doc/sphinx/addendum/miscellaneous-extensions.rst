Program derivation
==================

Rocq comes with an extension called ``Derive``, which supports program
derivation. Typically in the style of Bird and Meertens formalism or derivations
of program refinements. To use the Derive extension it must first be
required with ``From Corelib Require Derive``. When the extension is loaded,
it provides the following command:

.. cmd:: Derive @open_binders in @type as @ident
         Derive @open_binders SuchThat @type As @ident

   where :n:`@open_binders` is a list of the form
   :n:`@ident__i : @type__i` which can appear in :n:`@type`. This
   command opens a new proof presenting the user with a goal for
   :n:`@type` in which each name :n:`@ident__i` is bound to an
   existential variable of same name :g:`?ident__i` (these
   existential variables are shelved goals, as
   described in :tacn:`shelve`).

   When the proof is complete, Rocq defines :term:`constants <constant>`
   for each :n:`@ident__i` and for :n:`@ident`:

   + The first ones, named :n:`@ident__i`, are defined as the proof of the
     shelved goals (which are also the value of :n:`?ident__i`). They are always
     transparent.
   + The final one is named :n:`@ident`. It has type :n:`@type`, and its :term:`body` is
     the proof of the initially visible goal. It is opaque if the proof
     ends with :cmd:`Qed`, and transparent if the proof ends with :cmd:`Defined`.

.. example::

  .. rocqtop:: none

     Module Nat.
     Axiom mul_add_distr_l : forall n m p : nat, n * (m + p) = n * m + n * p.
     End Nat.

  .. rocqtop:: all

     From Corelib Require Derive.

     Section P.

     Variables (n m k:nat).

     Derive j p in ((k*n)+(k*m) = j*p) as h.
     Proof.
     rewrite <- Nat.mul_add_distr_l.
     subst j p.
     reflexivity.
     Qed.

     End P.

     Print j.
     Print p.
     Check h.

Any property can be used as `type`, not only an equation. In particular,
it could be an order relation specifying some form of program
refinement or a non-executable property from which deriving a program
is convenient.

.. note::
   The syntax :n:`Derive @open_binders SuchThat @type As @ident` is obsolete
   and to be avoided.
