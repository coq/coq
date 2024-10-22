.. _compil-steps:

==============================
How Rocq Processes Input Terms
==============================

It is in theory possible to write down every Gallina term explicitly
as described in the :ref:`Core Language <core-language>` part of this
manual, for instance
:n:`Nat.add (S O) (Nat.mul (S (S O)) (S (S O)))`. However, this would
be very tedious and error-prone and takes us away from our usual
mathematical practice. To circumvent this, Rocq offers multiple
preprocessing mechanisms to help fill the gap between what the users
would like to input to the system and the fully formal core language
expected by the kernel. We give an overview of all these steps below.

For instance, the notation mechanisms reflects the eponymous mathematical
practice and allows to write :n:`1 + 2 * 2` instead of the above
term. Those mechanisms range from simple :ref:`Abbreviations` to full
fledged :ref:`Notations` with user defined :ref:`syntaxes
<ReservingNotations>`. Multiple interpretations can be given to the
same syntax in different contexts thanks to the :ref:`scope
<Scopes>` mechanism. For instance :n:`(1 + 2 * 2)%N` can be
the above natural number expression while :n:`(1 + 2 * 2)%Z` can be
an expression with integers.

In order to take the best part of all these preprocessing mechanisms,
one needs a basic understanding of the multiple steps needed to
transform an inputted term (possibly with notations) into the valid
Gallina term which Rocq will ultimately use internally. Terms given as input
to Rocq go through several successive steps:

* During :gdef:`lexing` the input is split into a sequence of tokens,
  for instance the string ``"1 + 2 * 2"`` is split into the
  sequence of five tokens `'1' '+' '2' '*' '2'`. A set of :ref:`basic
  tokens <lexical-conventions>` are predefined and can be extended, in
  particular by :ref:`reserving notations <ReservingNotations>`.

* During :gdef:`parsing` the sequence of tokens is interpreted as a tree,
  for instance here:

  .. code-block:: text
     :name: after-parsing

             +
            / \
           1   *
              / \
             2   2

  The parsed grammar can be modified by :ref:`reserving notations
  <ReservingNotations>`.

* During :gdef:`internalization` a number of things are resolved. This
  includes :ref:`name resolution <qualified-names>`, :term:`notation
  interpretation` and introduction of :term:`holes <hole>` for :ref:`implicit
  arguments <ImplicitArguments>`.
  :gdef:`Notation interpretation <notation interpretation>`
  translates each syntactic element to a term,
  for instance :n:`1` can be interpreted as the
  natural number :n:`S O` then :n:`2` is interpreted as :n:`S (S O)`,
  then :n:`2 * 2` as :n:`Nat.mul (S (S O)) (S (S O))` and finally our
  whole term as :n:`Nat.add (S O) (Nat.mul (S (S O)) (S (S O)))`. The
  same expression can be given multiple interpretations in various
  contexts thanks to :ref:`Scopes`.

* Finally, :gdef:`pretyping`, can use the various mechanisms described in
  this section to fill gaps (for instance with :ref:`canonical structures
  <canonicalstructures>` or :ref:`typeclasses`) or fix terms (for
  instance with :ref:`coercions`) to obtain fully detailed terms in
  the :ref:`Core Language <core-language>`.

For each sentence, Rocq performs these steps successively and
independently. Once a step is completed, there is no going back. Then,
the result goes through the type checking phases discussed in
:ref:`previous chapter <core-language>`.
No types are involved at any point during the first three phases. And
reciprocally, none of the feature resolved during these phases, like
unqualified names, implicit arguments or notations, remains during the
later elaboration and type checking phases.

.. note::

   For developers and extension language users, the first two phases
   (:term:`lexing` and :term:`parsing`), together with a few more
   steps such as reading :cmd:`Reserved Notation`, are jointly called
   the syntax interpretation (ot synterp for short) phase, whereas
   internalization, elaboration and typechecking are called the
   interpretation phase. A document can thus be entirely parsed by
   running the synterp phase on it, without having to actually run any
   interpretation.

.. note::

   The :term:`pretyping` phase together with, all or part of, the
   previous steps is sometimes called elaboration in the literature.

.. note::

   Somme commands store terms for later use (for instance ``Ltac foo
   := exact some_term``), in this case they generally store the result
   of :term:`internalization`. The :term:`pretyping` is then run at
   use time.
