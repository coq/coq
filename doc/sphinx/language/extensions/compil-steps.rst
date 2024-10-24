.. _compil-steps:

======================
Main Compilation Steps
======================

It is in theory possible to write down every Gallina term explicitly
as described in the :ref:`Core Language <core-language>` part of this
manual, in the way they are understood by the kernel, for instance
:n:`Nat.add (S O) (Nat.mul (S (S O)) (S (S O)))`. However, this would
be very tedious and error-prone and takes us away from our usual
mathematical practice. To circumvent this, Rocq offers multiple
preprocessing mechanisms to help fill the gap between what the users
would like to input to the system and the fully formal core language
expected by the kernel.

For instance, the notation mechanisms reflects the eponym mathematical
practice and allows to write :n:`1 + 2 * 2` instead of the above
term. Those mechanisms range from simple :ref:`Abbreviations` to full
fledged :ref:`Notations` with user defined :ref:`syntaxes
<ReservingNotations>`. Multiple interpretations can be given to the
same syntax in different contexts thanks to the :ref:`scope
<Scopes>` mechanism. For instance :n:`(1 + 2 * 2)%N` could denote the
above natural number expression while :n:`(1 + 2 * 2)%Z` could denote
a similar expression with integers.

In order to take the best part of all these preprocessing mechanisms,
one needs a basic understanding of the multiple steps needed to
transform an inputed term (possibly with notations) into the valid
Gallina term which Rocq will ultimately use internally. When inputing
a term to Rocq, it goes through several successive steps:

* During :gdef:`lexing` the input is split into a sequence of tokens,
  for instance the string ``"1 + 2 * 2"`` will be split into the
  sequence of five tokens `'1' '+' '2' '*' '2'`. A set of :ref:`basic
  tokens <lexical-conventions>` are predefined and can be extended, in
  particular by :ref:`reserving notations <ReservingNotations>`.

* During :gdef:`parsing` the previous stream is given a tree-like
  structure, for instance here

  .. code-block:: text
     :name: after-parsing

             +
            / \
           1   *
              / \
             2   2

  The parsed grammar can be modified by :ref:`reserving notations
  <ReservingNotations>`.

* During :gdef:`notation interpretation` each syntactic element gets
  translated to a term, for instance :n:`1` can be interpreted as the
  natural number :n:`S O` then :n:`2` is interpreted as :n:`S (S O)`,
  then :n:`2 * 2` as :n:`Nat.mul (S (S O)) (S (S O))` and finally our
  whole term as :n:`Nat.add (S O) (Nat.mul (S (S O)) (S (S O)))`. The
  same expression can be given multiple interpretations in various
  contexts thanks to :ref:`Scopes`.

* Finally, :gdef:`elaboration` (also called :gdef:`pretyping` in the
  source code of Rocq) can use the various mechanisms described in
  this section to fill gaps (for instance with :ref:`implicit
  arguments <ImplicitArguments>`, :ref:`canonical structures
  <canonicalstructures>` or :ref:`typeclasses`) or fix terms (for
  instance with :ref:`coercions`) to obtain fully detailled terms in
  the :ref:`Core Language <core-language>`.

For each sentence, coq performs these steps successively and
independently. Once a step is completed, there is no going back. Then,
the result goes through the type checking phases discussed in
:ref:`previous chapter <core-language>`.
The first three phases (:term:`lexing`, :term:`parsing` and
:term:`notation interpretation`) are sometimes jointly called the
syntax interpretation (ot synterp for short) phase, whereas
elaboration and typechecking are called the interpretation phase.
No types are involved at any point during the synterp phase. And
reciprocally, no notation remains during the later elaboration and
type checking phases.
