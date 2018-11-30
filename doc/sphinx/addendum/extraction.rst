.. _extraction:

Extraction of programs in |OCaml| and Haskell
=============================================

:Authors: Jean-Christophe Filliâtre and Pierre Letouzey

We present here the |Coq| extraction commands, used to build certified
and relatively efficient functional programs, extracting them from
either |Coq| functions or |Coq| proofs of specifications. The
functional languages available as output are currently |OCaml|, Haskell
and Scheme. In the following, "ML" will be used (abusively) to refer
to any of the three.

Before using any of the commands or options described in this chapter,
the extraction framework should first be loaded explicitly
via ``Require Extraction``, or via the more robust
``From Coq Require Extraction``.
Note that in earlier versions of Coq, these commands and options were
directly available without any preliminary ``Require``.

.. coqtop:: in

   Require Extraction.

Generating ML Code
-------------------

.. note::

  In the following, a qualified identifier :token:`qualid`
  can be used to refer to any kind of |Coq| global "object" : constant,
  inductive type, inductive constructor or module name.

The next two commands are meant to be used for rapid preview of
extraction. They both display extracted term(s) inside |Coq|.

.. cmd:: Extraction @qualid

   Extraction of the mentioned object in the |Coq| toplevel.

.. cmd:: Recursive Extraction {+ @qualid }

   Recursive extraction of all the mentioned objects and
   all their dependencies in the |Coq| toplevel.

All the following commands produce real ML files. User can choose to
produce one monolithic file or one file per |Coq| library.

.. cmd:: Extraction @string {+ @qualid }

   Recursive extraction of all the mentioned objects and all
   their dependencies in one monolithic file :token:`string`.
   Global and local identifiers are renamed according to the chosen ML
   language to fulfill its syntactic conventions, keeping original
   names as much as possible.
  
.. cmd:: Extraction Library @ident

   Extraction of the whole |Coq| library :n:`@ident.v` to an ML module
   :n:`@ident.ml`. In case of name clash, identifiers are here renamed
   using prefixes ``coq_``  or ``Coq_`` to ensure a session-independent
   renaming.

.. cmd:: Recursive Extraction Library @ident

   Extraction of the |Coq| library :n:`@ident.v` and all other modules
   :n:`@ident.v` depends on.

.. cmd:: Separate Extraction {+ @qualid }

   Recursive extraction of all the mentioned objects and all
   their dependencies, just as :n:`Extraction @string {+ @qualid }`,
   but instead of producing one monolithic file, this command splits
   the produced code in separate ML files, one per corresponding Coq
   ``.v`` file. This command is hence quite similar to
   :cmd:`Recursive Extraction Library`, except that only the needed
   parts of Coq libraries are extracted instead of the whole.
   The naming convention in case of name clash is the same one as
   :cmd:`Extraction Library`: identifiers are here renamed using prefixes
   ``coq_``  or ``Coq_``.

The following command is meant to help automatic testing of
the extraction, see for instance the ``test-suite`` directory
in the |Coq| sources.

.. cmd:: Extraction TestCompile {+ @qualid }

   All the mentioned objects and all their dependencies are extracted
   to a temporary |OCaml| file, just as in ``Extraction "file"``. Then
   this temporary file and its signature are compiled with the same
   |OCaml| compiler used to built |Coq|. This command succeeds only
   if the extraction and the |OCaml| compilation succeed. It fails
   if the current target language of the extraction is not |OCaml|.

Extraction Options
-------------------

Setting the target language
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Extraction Language ( OCaml | Haskell | Scheme )
   :name: Extraction Language

   The ability to fix target language is the first and more important
   of the extraction options. Default is ``OCaml``.


Inlining and optimizations
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Since |OCaml| is a strict language, the extracted code has to
be optimized in order to be efficient (for instance, when using
induction principles we do not want to compute all the recursive calls
but only the needed ones). So the extraction mechanism provides an
automatic optimization routine that will be called each time the user
wants to generate an |OCaml| program. The optimizations can be split in two
groups: the type-preserving ones (essentially constant inlining and
reductions) and the non type-preserving ones (some function
abstractions of dummy types are removed when it is deemed safe in order
to have more elegant types). Therefore some constants may not appear in the
resulting monolithic |OCaml| program. In the case of modular extraction,
even if some inlining is done, the inlined constants are nevertheless
printed, to ensure session-independent programs.

Concerning Haskell, type-preserving optimizations are less useful
because of laziness. We still make some optimizations, for example in
order to produce more readable code.

The type-preserving optimizations are controlled by the following |Coq| options:

.. flag:: Extraction Optimize

   Default is on. This controls all type-preserving optimizations made on
   the ML terms (mostly reduction of dummy beta/iota redexes, but also
   simplifications on Cases, etc). Turn this option off if you want a
   ML term as close as possible to the Coq term.

.. flag:: Extraction Conservative Types

   Default is off. This controls the non type-preserving optimizations
   made on ML terms (which try to avoid function abstraction of dummy
   types). Turn this option on to make sure that ``e:t``
   implies that ``e':t'`` where ``e'`` and ``t'`` are the extracted
   code of ``e`` and ``t`` respectively.

.. flag:: Extraction KeepSingleton

   Default is off. Normally, when the extraction of an inductive type
   produces a singleton type (i.e. a type with only one constructor, and
   only one argument to this constructor), the inductive structure is
   removed and this type is seen as an alias to the inner type.
   The typical example is ``sig``. This option allows disabling this
   optimization when one wishes to preserve the inductive structure of types.

.. flag:: Extraction AutoInline

   Default is on. The extraction mechanism inlines the bodies of
   some defined constants, according to some heuristics
   like size of bodies, uselessness of some arguments, etc.
   Those heuristics are not always perfect; if you want to disable
   this feature, turn this option off.

.. cmd:: Extraction Inline {+ @qualid }

   In addition to the automatic inline feature, the constants
   mentionned by this command will always be inlined during extraction.

.. cmd:: Extraction NoInline {+ @qualid }

   Conversely, the constants mentionned by this command will
   never be inlined during extraction.

.. cmd:: Print Extraction Inline

   Prints the current state of the table recording the custom inlinings 
   declared by the two previous commands. 

.. cmd:: Reset Extraction Inline

   Empties the table recording the custom inlinings (see the
   previous commands).

**Inlining and printing of a constant declaration:**

The user can explicitly ask for a constant to be extracted by two means:

  * by mentioning it on the extraction command line

  * by extracting the whole |Coq| module of this constant.

In both cases, the declaration of this constant will be present in the
produced file. But this same constant may or may not be inlined in
the following terms, depending on the automatic/custom inlining mechanism.  

For the constants non-explicitly required but needed for dependency
reasons, there are two cases: 

  * If an inlining decision is taken, whether automatically or not,
    all occurrences of this constant are replaced by its extracted body,
    and this constant is not declared in the generated file.

  * If no inlining decision is taken, the constant is normally
    declared in the produced file. 

Extra elimination of useless arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following command provides some extra manual control on the
code elimination performed during extraction, in a way which
is independent but complementary to the main elimination
principles of extraction (logical parts and types).

.. cmd:: Extraction Implicit @qualid [ {+ @ident } ]

   This experimental command allows declaring some arguments of
   :token:`qualid` as implicit, i.e. useless in extracted code and hence to
   be removed by extraction. Here :token:`qualid` can be any function or
   inductive constructor, and the given :token:`ident` are the names of
   the concerned arguments. In fact, an argument can also be referred
   by a number indicating its position, starting from 1.

When an actual extraction takes place, an error is normally raised if the
:cmd:`Extraction Implicit` declarations cannot be honored, that is
if any of the implicit arguments still occurs in the final code.
This behavior can be relaxed via the following option:

.. flag:: Extraction SafeImplicits

   Default is on. When this option is off, a warning is emitted
   instead of an error if some implicit arguments still occur in the
   final code of an extraction. This way, the extracted code may be
   obtained nonetheless and reviewed manually to locate the source of the issue
   (in the code, some comments mark the location of these remaining implicit arguments).
   Note that this extracted code might not compile or run properly,
   depending of the use of these remaining implicit arguments.

Realizing axioms
~~~~~~~~~~~~~~~~

Extraction will fail if it encounters an informative axiom not realized. 
A warning will be issued if it encounters a logical axiom, to remind the
user that inconsistent logical axioms may lead to incorrect or
non-terminating extracted terms. 

It is possible to assume some axioms while developing a proof. Since
these axioms can be any kind of proposition or object or type, they may
perfectly well have some computational content. But a program must be
a closed term, and of course the system cannot guess the program which
realizes an axiom.  Therefore, it is possible to tell the system
what ML term corresponds to a given axiom. 

.. cmd:: Extract Constant @qualid => @string

   Give an ML extraction for the given constant.
   The :token:`string` may be an identifier or a quoted string.

.. cmd:: Extract Inlined Constant @qualid => @string

   Same as the previous one, except that the given ML terms will
   be inlined everywhere instead of being declared via a ``let``.

   .. note::
      This command is sugar for an :cmd:`Extract Constant` followed
      by a :cmd:`Extraction Inline`. Hence a :cmd:`Reset Extraction Inline`
      will have an effect on the realized and inlined axiom.

.. caution:: It is the responsibility of the user to ensure that the ML
   terms given to realize the axioms do have the expected types. In
   fact, the strings containing realizing code are just copied to the
   extracted files. The extraction recognizes whether the realized axiom
   should become a ML type constant or a ML object declaration. For example:

.. coqtop:: in

   Axiom X:Set.
   Axiom x:X.
   Extract Constant X => "int".
   Extract Constant x => "0".

Notice that in the case of type scheme axiom (i.e. whose type is an
arity, that is a sequence of product finished by a sort), then some type
variables have to be given (as quoted strings). The syntax is then:

.. cmdv:: Extract Constant @qualid @string ... @string => @string
   :undocumented:

The number of type variables is checked by the system. For example:

.. coqtop:: in

   Axiom Y : Set -> Set -> Set.
   Extract Constant Y "'a" "'b" => " 'a * 'b ".

Realizing an axiom via :cmd:`Extract Constant` is only useful in the
case of an informative axiom (of sort ``Type`` or ``Set``). A logical axiom
has no computational content and hence will not appear in extracted
terms. But a warning is nonetheless issued if extraction encounters a
logical axiom. This warning reminds user that inconsistent logical
axioms may lead to incorrect or non-terminating extracted terms.

If an informative axiom has not been realized before an extraction, a
warning is also issued and the definition of the axiom is filled with
an exception labeled ``AXIOM TO BE REALIZED``. The user must then
search these exceptions inside the extracted file and replace them by
real code.

Realizing inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~

The system also provides a mechanism to specify ML terms for inductive
types and constructors. For instance, the user may want to use the ML
native boolean type instead of the |Coq| one. The syntax is the following:

.. cmd:: Extract Inductive @qualid => @string [ {+ @string } ]

   Give an ML extraction for the given inductive type. You must specify
   extractions for the type itself (first :token:`string`) and all its
   constructors (all the :token:`string` between square brackets). In this form,
   the ML extraction must be an ML inductive datatype, and the native
   pattern matching of the language will be used.

.. cmdv:: Extract Inductive @qualid => @string [ {+ @string } ] @string

   Same as before, with a final extra :token:`string` that indicates how to
   perform pattern matching over this inductive type. In this form,
   the ML extraction could be an arbitrary type.
   For an inductive type with :math:`k` constructors, the function used to
   emulate the pattern matching should expect :math:`k+1` arguments, first the :math:`k`
   branches in functional form, and then the inductive element to
   destruct. For instance, the match branch ``| S n => foo`` gives the
   functional form ``(fun n -> foo)``. Note that a constructor with no
   arguments is considered to have one unit argument, in order to block
   early evaluation of the branch: ``| O => bar`` leads to the functional
   form ``(fun () -> bar)``. For instance, when extracting :g:`nat`
   into |OCaml| ``int``, the code to be provided has type:
   ``(unit->'a)->(int->'a)->int->'a``.

.. caution:: As for :cmd:`Extract Constant`, this command should be used with care:

  * The ML code provided by the user is currently **not** checked at all by
    extraction, even for syntax errors.

  * Extracting an inductive type to a pre-existing ML inductive type
    is quite sound. But extracting to a general type (by providing an
    ad-hoc pattern matching) will often **not** be fully rigorously
    correct. For instance, when extracting ``nat`` to |OCaml| ``int``,
    it is theoretically possible to build ``nat`` values that are
    larger than |OCaml| ``max_int``. It is the user's responsibility to
    be sure that no overflow or other bad events occur in practice.

  * Translating an inductive type to an arbitrary ML type does **not**
    magically improve the asymptotic complexity of functions, even if the
    ML type is an efficient representation. For instance, when extracting
    ``nat`` to |OCaml| ``int``, the function ``Nat.mul`` stays quadratic.
    It might be interesting to associate this translation with
    some specific :cmd:`Extract Constant` when primitive counterparts exist.

Typical examples are the following:

.. coqtop:: in
    
   Extract Inductive unit => "unit" [ "()" ].
   Extract Inductive bool => "bool" [ "true" "false" ].
   Extract Inductive sumbool => "bool" [ "true" "false" ].

.. note::

   When extracting to |OCaml|, if an inductive constructor or type has arity 2 and
   the corresponding string is enclosed by parentheses, and the string meets
   |OCaml|'s lexical criteria for an infix symbol, then the rest of the string is
   used as an infix constructor or type.

.. coqtop:: in
   
   Extract Inductive list => "list" [ "[]" "(::)" ].
   Extract Inductive prod => "(*)"  [ "(,)" ].

As an example of translation to a non-inductive datatype, let's turn
``nat`` into |OCaml| ``int`` (see caveat above):

.. coqtop:: in

   Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Avoiding conflicts with existing filenames
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When using :cmd:`Extraction Library`, the names of the extracted files
directly depend on the names of the |Coq| files. It may happen that
these filenames are in conflict with already existing files, 
either in the standard library of the target language or in other
code that is meant to be linked with the extracted code. 
For instance the module ``List`` exists both in |Coq| and in |OCaml|.
It is possible to instruct the extraction not to use particular filenames.

.. cmd:: Extraction Blacklist {+ @ident }

   Instruct the extraction to avoid using these names as filenames
   for extracted code.

.. cmd:: Print Extraction Blacklist

   Show the current list of filenames the extraction should avoid.

.. cmd:: Reset Extraction Blacklist

   Allow the extraction to use any filename.

For |OCaml|, a typical use of these commands is
``Extraction Blacklist String List``.

Differences between |Coq| and ML type systems
----------------------------------------------

Due to differences between |Coq| and ML type systems, 
some extracted programs are not directly typable in ML. 
We now solve this problem (at least in |OCaml|) by adding
when needed some unsafe casting ``Obj.magic``, which give
a generic type ``'a`` to any term.

First, if some part of the program is *very* polymorphic, there
may be no ML type for it. In that case the extraction to ML works
alright but the generated code may be refused by the ML
type checker. A very well known example is the ``distr-pair``
function:

.. coqtop:: in

   Definition dp {A B:Type}(x:A)(y:B)(f:forall C:Type, C->C) := (f A x, f B y).

In |OCaml|, for instance, the direct extracted term would be::

   let dp x y f = Pair((f () x),(f () y))

and would have type::

   dp : 'a -> 'a -> (unit -> 'a -> 'b) -> ('b,'b) prod

which is not its original type, but a restriction.

We now produce the following correct version::

   let dp x y f = Pair ((Obj.magic f () x), (Obj.magic f () y))

Secondly, some |Coq| definitions may have no counterpart in ML. This
happens when there is a quantification over types inside the type
of a constructor; for example:

.. coqtop:: in

   Inductive anything : Type := dummy : forall A:Set, A -> anything.

which corresponds to the definition of an ML dynamic type.
In |OCaml|, we must cast any argument of the constructor dummy
(no GADT are produced yet by the extraction).

Even with those unsafe castings, you should never get error like
``segmentation fault``. In fact even if your program may seem
ill-typed to the |OCaml| type checker, it can't go wrong : it comes
from a Coq well-typed terms, so for example inductive types will always 
have the correct number of arguments, etc. Of course, when launching
manually some extracted function, you should apply it to arguments
of the right shape (from the |Coq| point-of-view).

More details about the correctness of the extracted programs can be 
found in :cite:`Let02`.

We have to say, though, that in most "realistic" programs, these problems do not
occur. For example all the programs of Coq library are accepted by the |OCaml|
type checker without any ``Obj.magic`` (see examples below).

Some examples
-------------

We present here two examples of extraction, taken from the
|Coq| Standard Library. We choose |OCaml| as the target language,
but everything, with slight modifications, can also be done in the
other languages supported by extraction.
We then indicate where to find other examples and tests of extraction.

A detailed example: Euclidean division
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The file ``Euclid`` contains the proof of Euclidean division.
The natural numbers used here are unary, represented by the type``nat``,
which is defined by two constructors ``O`` and ``S``.
This module contains a theorem ``eucl_dev``, whose type is::

   forall b:nat, b > 0 -> forall a:nat, diveucl a b

where ``diveucl`` is a type for the pair of the quotient and the
modulo, plus some logical assertions that disappear during extraction.
We can now extract this program to |OCaml|:

.. coqtop:: none

   Reset Initial.

.. coqtop:: all

   Require Extraction.
   Require Import Euclid Wf_nat.
   Extraction Inline gt_wf_rec lt_wf_rec induction_ltof2.
   Recursive Extraction eucl_dev.

The inlining of ``gt_wf_rec`` and others is not
mandatory. It only enhances readability of extracted code.
You can then copy-paste the output to a file ``euclid.ml`` or let 
|Coq| do it for you with the following command::

   Extraction "euclid" eucl_dev.

Let us play the resulting program (in an |OCaml| toplevel)::

   #use "euclid.ml";;
   type nat = O | S of nat
   type sumbool = Left | Right
   val sub : nat -> nat -> nat = <fun>
   val le_lt_dec : nat -> nat -> sumbool = <fun>
   val le_gt_dec : nat -> nat -> sumbool = <fun>
   type diveucl = Divex of nat * nat
   val eucl_dev : nat -> nat -> diveucl = <fun>

   # eucl_dev (S (S O)) (S (S (S (S (S O)))));;
   - : diveucl = Divex (S (S O), S O)

It is easier to test on |OCaml| integers::

   # let rec nat_of_int = function 0 -> O | n -> S (nat_of_int (n-1));;
   val nat_of_int : int -> nat = <fun>

   # let rec int_of_nat = function O -> 0 | S p -> 1+(int_of_nat p);;
   val int_of_nat : nat -> int = <fun>

   # let div a b = 
     let Divex (q,r) = eucl_dev (nat_of_int b) (nat_of_int a)
     in (int_of_nat q, int_of_nat r);;
   val div : int -> int -> int * int = <fun>

   # div 173 15;;
   - : int * int = (11, 8)

Note that these ``nat_of_int`` and ``int_of_nat`` are now
available via a mere ``Require Import ExtrOcamlIntConv`` and then
adding these functions to the list of functions to extract. This file
``ExtrOcamlIntConv.v`` and some others in ``plugins/extraction/``
are meant to help building concrete program via extraction.

Extraction's horror museum
~~~~~~~~~~~~~~~~~~~~~~~~~~

Some pathological examples of extraction are grouped in the file
``test-suite/success/extraction.v`` of the sources of |Coq|.

Users' Contributions
~~~~~~~~~~~~~~~~~~~~

Several of the |Coq| Users' Contributions use extraction to produce
certified programs. In particular the following ones have an automatic
extraction test:

 * ``additions`` : https://github.com/coq-contribs/additions
 * ``bdds`` : https://github.com/coq-contribs/bdds
 * ``canon-bdds`` : https://github.com/coq-contribs/canon-bdds
 * ``chinese`` : https://github.com/coq-contribs/chinese
 * ``continuations`` : https://github.com/coq-contribs/continuations
 * ``coq-in-coq`` : https://github.com/coq-contribs/coq-in-coq
 * ``exceptions`` : https://github.com/coq-contribs/exceptions
 * ``firing-squad`` : https://github.com/coq-contribs/firing-squad
 * ``founify`` : https://github.com/coq-contribs/founify
 * ``graphs`` : https://github.com/coq-contribs/graphs
 * ``higman-cf`` : https://github.com/coq-contribs/higman-cf
 * ``higman-nw`` : https://github.com/coq-contribs/higman-nw
 * ``hardware`` : https://github.com/coq-contribs/hardware
 * ``multiplier`` : https://github.com/coq-contribs/multiplier
 * ``search-trees`` : https://github.com/coq-contribs/search-trees
 * ``stalmarck`` : https://github.com/coq-contribs/stalmarck

Note that ``continuations`` and ``multiplier`` are a bit particular. They are
examples of developments where ``Obj.magic`` is needed. This is
probably due to a heavy use of impredicativity. After compilation, those
two examples run nonetheless, thanks to the correction of the
extraction :cite:`Let02`.
