.. _history:

----------------------
Early history of Coq
----------------------

The Rocq Prover is the successor of Coq, whose history, up to version 7, is presented here.

Historical roots
----------------

Coq is a proof assistant for higher-order logic, allowing the
development of computer programs consistent with their formal
specification. It is the result of about ten years [#years]_ of research
of the Coq project. We shall briefly survey here three main aspects: the
*logical language* in which we write our axiomatizations and
specifications, the *proof assistant* which allows the development of
verified mathematical proofs, and the *program extractor* which
synthesizes computer programs obeying their formal specifications,
written as logical assertions in the language.

The logical language used by Coq is a variety of type theory, called the
*Calculus of Inductive Constructions*. Without going back to Leibniz and
Boole, we can date the creation of what is now called mathematical logic
to the work of Frege and Peano at the turn of the century. The discovery
of antinomies in the free use of predicates or comprehension principles
prompted Russell to restrict predicate calculus with a stratification of
*types*. This effort culminated with *Principia Mathematica*, the first
systematic attempt at a formal foundation of mathematics. A
simplification of this system along the lines of simply typed
λ-calculus occurred with Church’s *Simple Theory of
Types*. The λ-calculus notation, originally used for
expressing functionality, could also be used as an encoding of natural
deduction proofs. This Curry-Howard isomorphism was used by N. de Bruijn
in the *Automath* project, the first full-scale attempt to develop and
mechanically verify mathematical proofs. This effort culminated with
Jutting’s verification of Landau’s *Grundlagen* in the 1970’s.
Exploiting this Curry-Howard isomorphism, notable achievements in proof
theory saw the emergence of two type-theoretic frameworks; the first
one, Martin-Löf’s *Intuitionistic Theory of Types*, attempts a new
foundation of mathematics on constructive principles. The second one,
Girard’s polymorphic λ-calculus :math:`F_\omega`, is a
very strong functional system in which we may represent higher-order
logic proof structures. Combining both systems in a higher-order
extension of the Automath language, T. Coquand presented in 1985 the
first version of the *Calculus of Constructions*, CoC. This strong
logical system allowed powerful axiomatizations, but direct inductive
definitions were not possible, and inductive notions had to be defined
indirectly through functional encodings, which introduced inefficiencies
and awkwardness. The formalism was extended in 1989 by T. Coquand and C.
Paulin with primitive inductive definitions, leading to the current
*Calculus of Inductive Constructions*. This extended formalism is not
rigorously defined here. Rather, numerous concrete examples are
discussed. We refer the interested reader to relevant research papers
for more information about the formalism, its meta-theoretic properties,
and semantics. However, it should not be necessary to understand this
theoretical material in order to write specifications. It is possible to
understand the Calculus of Inductive Constructions at a higher level, as
a mixture of predicate calculus, inductive predicate definitions
presented as typed PROLOG, and recursive function definitions close to
the language ML.

Automated theorem-proving was pioneered in the 1960’s by Davis and
Putnam in propositional calculus. A complete mechanization (in the sense
of a semidecision procedure) of classical first-order logic was
proposed in 1965 by J.A. Robinson, with a single uniform inference rule
called *resolution*. Resolution relies on solving equations in free
algebras (i.e. term structures), using the *unification algorithm*. Many
refinements of resolution were studied in the 1970’s, but few convincing
implementations were realized, except of course that PROLOG is in some
sense issued from this effort. A less ambitious approach to proof
development is computer-aided proof-checking. The most notable
proof-checkers developed in the 1970’s were LCF, designed by R. Milner
and his colleagues at U. Edinburgh, specialized in proving properties
about denotational semantics recursion equations, and the Boyer and
Moore theorem-prover, an automation of primitive recursion over
inductive data types. While the Boyer-Moore theorem-prover attempted to
synthesize proofs by a combination of automated methods, LCF constructed
its proofs through the programming of *tactics*, written in a high-level
functional meta-language, ML.

The salient feature which clearly distinguishes our proof assistant from
say LCF or Boyer and Moore’s, is its possibility to extract programs
from the constructive contents of proofs. This computational
interpretation of proof objects, in the tradition of Bishop’s
constructive mathematics, is based on a realizability interpretation, in
the sense of Kleene, due to C. Paulin. The user must just mark his
intention by separating in the logical statements the assertions stating
the existence of a computational object from the logical assertions
which specify its properties, but which may be considered as just
comments in the corresponding program. Given this information, the
system automatically extracts a functional term from a consistency proof
of its specifications. This functional term may be in turn compiled into
an actual computer program. This methodology of extracting programs from
proofs is a revolutionary paradigm for software engineering. Program
synthesis has long been a theme of research in artificial intelligence,
pioneered by R. Waldinger. The Tablog system of Z. Manna and R.
Waldinger allows the deductive synthesis of functional programs from
proofs in tableau form of their specifications, written in a variety of
first-order logic. Development of a systematic *programming logic*,
based on extensions of Martin-Löf’s type theory, was undertaken at
Cornell U. by the Nuprl team, headed by R. Constable. The first actual
program extractor, PX, was designed and implemented around 1985 by S.
Hayashi from Kyoto University. It allows the extraction of a LISP
program from a proof in a logical system inspired by the logical
formalisms of S. Feferman. Interest in this methodology is growing in
the theoretical computer science community. We can foresee the day when
actual computer systems used in applications will contain certified
modules, automatically generated from a consistency proof of their
formal specifications. We are however still far from being able to use
this methodology in a smooth interaction with the standard tools from
software engineering, i.e. compilers, linkers, run-time systems taking
advantage of special hardware, debuggers, and the like. We hope that Coq
can be of use to researchers interested in experimenting with this new
methodology.

.. [#years] At the time of writing, i.e. 1995.

Versions 1 to 5
---------------

.. note::
   This summary was written in 1995 together with the previous
   section and formed the initial version of the Credits chapter.

   A more comprehensive description of these early versions is available
   in the following subsections, which come from a document written in
   September 2015 by Gérard Huet, Thierry Coquand and Christine Paulin.

A first implementation of CoC was started in 1984 by G. Huet and T.
Coquand. Its implementation language was CAML, a functional programming
language from the ML family designed at INRIA in Rocquencourt. The core
of this system was a proof-checker for CoC seen as a typed
λ-calculus, called the *Constructive Engine*. This engine
was operated through a high-level notation permitting the declaration of
axioms and parameters, the definition of mathematical types and objects,
and the explicit construction of proof objects encoded as
λ-terms. A section mechanism, designed and implemented by
G. Dowek, allowed hierarchical developments of mathematical theories.
This high-level language was called the *Mathematical Vernacular*.
Furthermore, an interactive *Theorem Prover* permitted the incremental
construction of proof trees in a top-down manner, subgoaling recursively
and backtracking from dead-ends. The theorem prover executed tactics
written in CAML, in the LCF fashion. A basic set of tactics was
predefined, which the user could extend by his own specific tactics.
This system (Version 4.10) was released in 1989. Then, the system was
extended to deal with the new calculus with inductive types by C.
Paulin, with corresponding new tactics for proofs by induction. A new
standard set of tactics was streamlined, and the vernacular extended for
tactics execution. A package to compile programs extracted from proofs
to actual computer programs in CAML or some other functional language
was designed and implemented by B. Werner. A new user-interface, relying
on a CAML-X interface by D. de Rauglaudre, was designed and implemented
by A. Felty. It allowed operation of the theorem-prover through the
manipulation of windows, menus, mouse-sensitive buttons, and other
widgets. This system (Version 5.6) was released in 1991.

Coq was ported to the new implementation Caml-light of X. Leroy and D.
Doligez by D. de Rauglaudre (Version 5.7) in 1992. A new version of Coq
was then coordinated by C. Murthy, with new tools designed by C. Parent
to prove properties of ML programs (this methodology is dual to program
extraction) and a new user-interaction loop. This system (Version 5.8)
was released in May 1993. A Centaur interface CTCoq was then developed
by Y. Bertot from the Croap project from INRIA-Sophia-Antipolis.

In parallel, G. Dowek and H. Herbelin developed a new proof engine,
allowing the general manipulation of existential variables consistently
with dependent types in an experimental version of Coq (V5.9).

The version V5.10 of Coq is based on a generic system for manipulating
terms with binding operators due to Chet Murthy. A new proof engine
allows the parallel development of partial proofs for independent
subgoals. The structure of these proof trees is a mixed representation
of derivation trees for the Calculus of Inductive Constructions with
abstract syntax trees for the tactics scripts, allowing the navigation
in a proof at various levels of details. The proof engine allows generic
environment items managed in an object-oriented way. This new
architecture, due to C. Murthy, supports several new facilities which
make the system easier to extend and to scale up:

-  User-programmable tactics are allowed

-  It is possible to separately verify development modules, and to load
   their compiled images without verifying them again - a quick
   relocation process allows their fast loading

-  A generic parsing scheme allows user-definable notations, with a
   symmetric table-driven pretty-printer

-  Syntactic definitions allow convenient abbreviations

-  A limited facility of meta-variables allows the automatic synthesis
   of certain type expressions, allowing generic notations for e.g.
   equality, pairing, and existential quantification.

In the Fall of 1994, C. Paulin-Mohring replaced the structure of
inductively defined types and families by a new structure, allowing the
mutually recursive definitions. P. Manoury implemented a translation of
recursive definitions into the primitive recursive style imposed by the
internal recursion operators, in the style of the ProPre system. C.
Muñoz implemented a decision procedure for intuitionistic propositional
logic, based on results of R. Dyckhoff. J.C. Filliâtre implemented a
decision procedure for first-order logic without contraction, based on
results of J. Ketonen and R. Weyhrauch. Finally C. Murthy implemented a
library of inversion tactics, relieving the user from tedious
definitions of “inversion predicates”.

| Rocquencourt, Feb. 1st 1995
| Gérard Huet
|

Version 1
~~~~~~~~~

This software is a prototype type checker for a higher-order logical
formalism known as the Theory of Constructions, presented in his PhD
thesis by Thierry Coquand, with influences from Girard's system F and
de Bruijn's Automath.  The metamathematical analysis of the system is
the PhD work of Thierry Coquand. The software is mostly the work of
Gérard Huet.  Most of the mathematical examples verified with the
software are due to Thierry Coquand.

The programming language of the CONSTR software (as it was called at
the time) was a version of ML adapted from the Edinburgh LCF system
and running on a LISP backend. The main improvements from the original
LCF ML were that ML was compiled rather than interpreted (Gérard Huet
building on the original translator by Lockwood Morris), and that it
was enriched by recursively defined types (work of Guy
Cousineau). This ancestor of CAML was used and improved by Larry
Paulson for his implementation of Cambridge LCF.

Software developments of this prototype occurred from late 1983 to
early 1985.

Version 1.10 was frozen on December 22nd 1984. It is the version used
for the examples in Thierry Coquand's thesis, defended on January 31st
1985. There was a unique binding operator, used both for universal
quantification (dependent product) at the level of types and
functional abstraction (λ) at the level of terms/proofs, in the manner
of Automath. Substitution (λ-reduction) was implemented using de
Bruijn's indexes.

Version 1.11 was frozen on February 19th, 1985. It is the version used
for the examples in the paper: T. Coquand, G. Huet. *Constructions: A
Higher Order Proof System for Mechanizing Mathematics* :cite:`CH85`.

Christine Paulin joined the team at this point, for her DEA research
internship.  In her DEA memoir (August 1985) she presents developments
for the *lambo* function – :math:`\text{lambo}(f)(n)` computes the minimal
:math:`m` such that :math:`f(m)` is greater than :math:`n`, for :math:`f`
an increasing integer function, a challenge for constructive mathematics.
She also encoded the majority voting algorithm of Boyer and Moore.

Version 2
~~~~~~~~~

The formal system, now renamed as the *Calculus of Constructions*, was
presented with a proof of consistency and comparisons with proof
systems of Per Martin Löf, Girard, and the Automath family of N. de
Bruijn, in the paper: T. Coquand and G. Huet. *The Calculus of
Constructions* :cite:`CH88`.

An abstraction of the software design, in the form of an abstract
machine for proof checking, and a fuller sequence of mathematical
developments was presented in: T. Coquand, G. Huet. *Concepts
Mathématiques et Informatiques Formalisés dans le Calcul des
Constructions* :cite:`CH87`.

Version 2.8 was frozen on December 16th, 1985, and served for
developing the examples in the above papers.

This calculus was then enriched in version 2.9 with a cumulative
hierarchy of universes. Universe levels were initially explicit
natural numbers.  Another improvement was the possibility of automatic
synthesis of implicit type arguments, relieving the user of tedious
redundant declarations.

Christine Paulin wrote an article *Algorithm development in the
Calculus of Constructions* :cite:`P86`. Besides *lambo* and *majority*,
she presents *quicksort* and a text formatting algorithm.

Version 2.13 of the Calculus of Constructions with universes was
frozen on June 25th, 1986.

A synthetic presentation of type theory along constructive lines with
ML algorithms was given by Gérard Huet in his May 1986 CMU course
notes *Formal Structures for Computation and Deduction*. Its chapter
*Induction and Recursion in the Theory of Constructions* was presented
as an invited paper at the Joint Conference on Theory and Practice of
Software Development TAPSOFT’87 at Pise in March 1987, and published
as *Induction Principles Formalized in the Calculus of
Constructions* :cite:`H88`.

Version 3
~~~~~~~~~

This version saw the beginning of proof automation, with a search
algorithm inspired from PROLOG and the applicative logic programming
programs of the course notes *Formal structures for computation and
deduction*.  The search algorithm was implemented in ML by Thierry
Coquand.  The proof system could thus be used in two modes: proof
verification and proof synthesis, with tactics such as ``AUTO``.

The implementation language was now called CAML, for Categorical
Abstract Machine Language. It used as backend the LLM3 virtual machine
of Le Lisp by Jérôme Chailloux. The main developers of CAML were
Michel Mauny, Ascander Suarez and Pierre Weis.

V3.1 was started in the summer of 1986, V3.2 was frozen at the end of
November 1986. V3.4 was developed in the first half of 1987.

Thierry Coquand held a post-doctoral position in Cambridge University
in 1986-87, where he developed a variant implementation in SML, with
which he wrote some developments on fixpoints in Scott's domains.

Version 4
~~~~~~~~~

This version saw the beginning of program extraction from proofs, with
two varieties of the type ``Prop`` of propositions, indicating
constructive intent.  The proof extraction algorithms were implemented
by Christine Paulin-Mohring.

V4.1 was frozen on July 24th, 1987. It had a first identified library
of mathematical developments (directory ``exemples``), with libraries
``Logic`` (containing impredicative encodings of intuitionistic logic and
algebraic primitives for booleans, natural numbers and list), ``Peano``
developing second-order Peano arithmetic, ``Arith`` defining addition,
multiplication, euclidean division and factorial. Typical developments
were the Knaster-Tarski theorem and Newman's lemma from rewriting
theory.

V4.2 was a joint development of a team consisting of Thierry Coquand,
Gérard Huet and Christine Paulin-Mohring. A file V4.2.log records the
log of changes.  It was frozen on September 1987 as the last version
implemented in CAML 2.3, and V4.3 followed on CAML 2.5, a more stable
development system.

V4.3 saw the first top-level of the system. Instead of evaluating
explicit quotations, the user could develop his mathematics in a
high-level language called the mathematical vernacular (following
Automath terminology).  The user could develop files in the vernacular
notation (with ``.v`` extension) which were now separate from the ``ml``
sources of the implementation.  Gilles Dowek joined the team to
develop the vernacular language as his DEA internship research.

A notion of sticky constant was introduced, in order to keep names of
lemmas when local hypotheses of proofs were discharged. This gave a
notion of global mathematical environment with local sections.

Another significant practical change was that the system, originally
developed on the VAX central computer of our lab, was transferred on
SUN personal workstations, allowing a level of distributed
development.  The extraction algorithm was modified, with three
annotations ``Pos``, ``Null`` and ``Typ`` decorating the sorts ``Prop``
and ``Type``.

Version 4.3 was frozen at the end of November 1987, and was
distributed to an early community of users (among those were Hugo
Herbelin and Loic Colson).

V4.4 saw the first version of (encoded) inductive types.  Now natural
numbers could be defined as::

  [source, coq]
  Inductive NAT : Prop = O : NAT | Succ : NAT->NAT.

These inductive types were encoded impredicatively in the calculus,
using a subsystem *rec* due to Christine Paulin.  V4.4 was frozen on
March 6th 1988.

Version 4.5 was the first one to support inductive types and program
extraction.  Its banner was *Calcul des Constructions avec
Réalisations et Synthèse*.  The vernacular language was enriched to
accommodate extraction commands.

The verification engine design was presented as: G. Huet. *The
Constructive Engine*. Version 4.5. Invited Conference, 2nd European
Symposium on Programming, Nancy, March 88.  The final paper,
describing the V4.9 implementation, appeared in: A perspective in
Theoretical Computer Science, Commemorative Volume in memory of Gift
Siromoney, Ed. R. Narasimhan, World Scientific Publishing, 1989.

Version 4.5 was demonstrated in June 1988 at the YoP Institute on
Logical Foundations of Functional Programming organized by Gérard Huet
at Austin, Texas.

Version 4.6 was started during the summer of 1988. Its main
improvement was the complete rehaul of the proof synthesis engine by
Thierry Coquand, with a tree structure of goals.

Its source code was communicated to Randy Pollack on September 2nd
1988.  It evolved progressively into LEGO, proof system for Luo's
formalism of Extended Calculus of Constructions.

The discharge tactic was modified by Gérard Huet to allow for
inter-dependencies in discharged lemmas. Christine Paulin improved the
inductive definition scheme in order to accommodate predicates of any
arity.

Version 4.7 was started on September 6th, 1988.

This version starts exploiting the CAML notion of module in order to
improve the modularity of the implementation. Now the term verifier is
identified as a proper module Machine, which the structure of its
internal data structures being hidden and thus accessible only through
the legitimate operations.  This machine (the constructive engine) was
the trusted core of the implementation. The proof synthesis mechanism
was a separate proof term generator. Once a complete proof term was
synthesized with the help of tactics, it was entirely re-checked by
the engine. Thus there was no need to certify the tactics, and the
system took advantage of this fact by having tactics ignore the
universe levels, universe consistency check being relegated to the
final type checking pass. This induced a certain puzzlement in early
users who saw, after a successful proof search, their ``QED`` followed
by silence, followed by a failure message due to a universe
inconsistency…

The set of examples comprise set theory experiments by Hugo Herbelin,
and notably the Schroeder-Bernstein theorem.

Version 4.8, started on October 8th, 1988, saw a major
re-implementation of the abstract syntax type ``constr``, separating
variables of the formalism and metavariables denoting incomplete terms
managed by the search mechanism.  A notion of level (with three values
``TYPE``, ``OBJECT`` and ``PROOF``) is made explicit and a type judgement
clarifies the constructions, whose implementation is now fully
explicit. Structural equality is speeded up by using pointer equality,
yielding spectacular improvements. Thierry Coquand adapts the proof
synthesis to the new representation, and simplifies pattern matching
to first-order predicate calculus matching, with important performance
gain.

A new representation of the universe hierarchy is then defined by
Gérard Huet.  Universe levels are now implemented implicitly, through
a hidden graph of abstract levels constrained with an order relation.
Checking acyclicity of the graph insures well-foundedness of the
ordering, and thus consistency. This was documented in a memo *Adding
Type:Type to the Calculus of Constructions* which was never published.

The development version is released as a stable 4.8 at the end of
1988.

Version 4.9 is released on March 1st 1989, with the new "elastic"
universe hierarchy.

The spring of 1989 saw the first attempt at documenting the system
usage, with a number of papers describing the formalism:

- *Metamathematical Investigations of a Calculus of Constructions*, by
  Thierry Coquand :cite:`C90`,

- *Inductive definitions in the Calculus of Constructions*, by
  Christine Paulin-Mohrin,

- *Extracting Fω's programs from proofs in the Calculus of
  Constructions*, by Christine Paulin-Mohring* :cite:`P89`,

- *The Constructive Engine*, by Gérard Huet :cite:`H89`,

as well as a number of user guides:

- *A short user's guide for the Constructions*, Version 4.10, by Gérard Huet
- *A Vernacular Syllabus*, by Gilles Dowek.
- *The Tactics Theorem Prover, User's guide*, Version 4.10, by Thierry
  Coquand.

Stable V4.10, released on May 1st, 1989, was then a mature system,
distributed with CAML V2.6.

In the mean time, Thierry Coquand and Christine Paulin-Mohring had
been investigating how to add native inductive types to the Calculus
of Constructions, in the manner of Per Martin-Löf's Intuitionistic
Type Theory. The impredicative encoding had already been presented in:
F. Pfenning and C. Paulin-Mohring. *Inductively defined types in the
Calculus of Constructions* :cite:`PP90`. An extension of the calculus
with primitive inductive types appeared in: T. Coquand and
C. Paulin-Mohring. *Inductively defined types* :cite:`CP90`.

This led to the Calculus of Inductive Constructions, logical formalism
implemented in Versions 5 upward of the system, and documented in:
C. Paulin-Mohring. *Inductive Definitions in the System Coq - Rules
and Properties* :cite:`P93`.

The last version of CONSTR is Version 4.11, which was last distributed
in the spring of 1990. It was demonstrated at the first workshop of
the European Basic Research Action Logical Frameworks In Sophia
Antipolis in May 1990.

Version 5
~~~~~~~~~

At the end of 1989, Version 5.1 was started, and renamed as the system
Coq for the Calculus of Inductive Constructions. It was then ported to
the new stand-alone implementation of ML called Caml-light.

In 1990 many changes occurred. Thierry Coquand left for Chalmers
University in Göteborg. Christine Paulin-Mohring took a CNRS
researcher position at the LIP laboratory of École Normale Supérieure
de Lyon. Project Formel was terminated, and gave rise to two teams:
Cristal at INRIA-Roquencourt, that continued developments in
functional programming with Caml-light then OCaml, and Coq, continuing
the type theory research, with a joint team headed by Gérard Huet at
INRIA-Rocquencourt and Christine Paulin-Mohring at the LIP laboratory
of CNRS-ENS Lyon.

Chetan Murthy joined the team in 1991 and became the main software
architect of Version 5. He completely rehauled the implementation for
efficiency.  Versions 5.6 and 5.8 were major distributed versions,
with complete documentation and a library of users' developments. The
use of the RCS revision control system, and systematic ChangeLog
files, allow a more precise tracking of the software developments.

| September 2015 +
| Thierry Coquand, Gérard Huet and Christine Paulin-Mohring.
|

Versions 6
----------

Version 6.1
~~~~~~~~~~~

The present version 6.1 of Coq is based on the V5.10 architecture. It
was ported to the new language Objective Caml by Bruno Barras. The
underlying framework has slightly changed and allows more conversions
between sorts.

The new version provides powerful tools for easier developments.

Cristina Cornes designed an extension of the Coq syntax to allow
definition of terms using a powerful pattern matching analysis in the
style of ML programs.

Amokrane Saïbi wrote a mechanism to simulate inheritance between types
families extending a proposal by Peter Aczel. He also developed a
mechanism to automatically compute which arguments of a constant may be
inferred by the system and consequently do not need to be explicitly
written.

Yann Coscoy designed a command which explains a proof term using natural
language. Pierre Crégut built a new tactic which solves problems in
quantifier-free Presburger Arithmetic. Both functionalities have been
integrated to the Coq system by Hugo Herbelin.

Samuel Boutin designed a tactic for simplification of commutative rings
using a canonical set of rewriting rules and equality modulo
associativity and commutativity.

Finally the organisation of the Coq distribution has been supervised by
Jean-Christophe Filliâtre with the help of Judicaël Courant and Bruno
Barras.

| Lyon, Nov. 18th 1996
| Christine Paulin
|

Version 6.2
~~~~~~~~~~~

In version 6.2 of Coq, the parsing is done using camlp4, a preprocessor
and pretty-printer for CAML designed by Daniel de Rauglaudre at INRIA.
Daniel de Rauglaudre made the first adaptation of Coq for camlp4, this
work was continued by Bruno Barras who also changed the structure of Coq
abstract syntax trees and the primitives to manipulate them. The result
of these changes is a faster parsing procedure with greatly improved
syntax-error messages. The user-interface to introduce grammar or
pretty-printing rules has also changed.

Eduardo Giménez redesigned the internal tactic libraries, giving uniform
names to Caml functions corresponding to Coq tactic names.

Bruno Barras wrote new, more efficient reduction functions.

Hugo Herbelin introduced more uniform notations in the Coq specification
language: the definitions by fixpoints and pattern matching have a more
readable syntax. Patrick Loiseleur introduced user-friendly notations
for arithmetic expressions.

New tactics were introduced: Eduardo Giménez improved the mechanism to
introduce macros for tactics, and designed special tactics for
(co)inductive definitions; Patrick Loiseleur designed a tactic to
simplify polynomial expressions in an arbitrary commutative ring which
generalizes the previous tactic implemented by Samuel Boutin.
Jean-Christophe Filliâtre introduced a tactic for refining a goal, using
a proof term with holes as a proof scheme.

David Delahaye designed the tool to search an object in the library
given its type (up to isomorphism).

Henri Laulhère produced the Coq distribution for the Windows
environment.

Finally, Hugo Herbelin was the main coordinator of the Coq documentation
with principal contributions by Bruno Barras, David Delahaye,
Jean-Christophe Filliâtre, Eduardo Giménez, Hugo Herbelin and Patrick
Loiseleur.

| Orsay, May 4th 1998
| Christine Paulin
|

Version 6.3
~~~~~~~~~~~

The main changes in version V6.3 were the introduction of a few new
tactics and the extension of the guard condition for fixpoint
definitions.

B. Barras extended the unification algorithm to complete partial terms
and fixed various tricky bugs related to universes.

D. Delahaye developed the ``AutoRewrite`` tactic. He also designed the
new behavior of ``Intro`` and provided the tacticals ``First`` and
``Solve``.

J.-C. Filliâtre developed the ``Correctness`` tactic.

\E. Giménez extended the guard condition in fixpoints.

H. Herbelin designed the new syntax for definitions and extended the
``Induction`` tactic.

P. Loiseleur developed the ``Quote`` tactic and the new design of the
``Auto`` tactic, he also introduced the index of errors in the
documentation.

C. Paulin wrote the ``Focus`` command and introduced the reduction
functions in definitions, this last feature was proposed by J.-F.
Monin from CNET Lannion.

| Orsay, Dec. 1999
| Christine Paulin
|

Versions 7
----------

Summary of changes
~~~~~~~~~~~~~~~~~~

The version V7 is a new implementation started in September 1999 by
Jean-Christophe Filliâtre. This is a major revision with respect to the
internal architecture of the system. The Coq version 7.0 was distributed
in March 2001, version 7.1 in September 2001, version 7.2 in January
2002, version 7.3 in May 2002 and version 7.4 in February 2003.

Jean-Christophe Filliâtre designed the architecture of the new system.
He introduced a new representation for environments and wrote a new
kernel for type checking terms. His approach was to use functional
data-structures in order to get more sharing, to prepare the addition of
modules and also to get closer to a certified kernel.

Hugo Herbelin introduced a new structure of terms with local
definitions. He introduced “qualified” names, wrote a new
pattern matching compilation algorithm and designed a more compact
algorithm for checking the logical consistency of universes. He
contributed to the simplification of Coq internal structures and the
optimisation of the system. He added basic tactics for forward reasoning
and coercions in patterns.

David Delahaye introduced a new language for tactics. General tactics
using pattern matching on goals and context can directly be written from
the Coq toplevel. He also provided primitives for the design of
user-defined tactics in Caml.

Micaela Mayero contributed the library on real numbers. Olivier
Desmettre extended this library with axiomatic trigonometric functions,
square, square roots, finite sums, Chasles property and basic plane
geometry.

Jean-Christophe Filliâtre and Pierre Letouzey redesigned a new
extraction procedure from Coq terms to Caml or Haskell programs. This
new extraction procedure, unlike the one implemented in previous version
of Coq is able to handle all terms in the Calculus of Inductive
Constructions, even involving universes and strong elimination. P.
Letouzey adapted user contributions to extract ML programs when it was
sensible. Jean-Christophe Filliâtre wrote ``coqdoc`` (now ``rocq doc``), a documentation
tool for Coq libraries usable from version 7.2.

Bruno Barras improved the efficiency of the reduction algorithm and the
confidence level in the correctness of Coq critical type checking
algorithm.

Yves Bertot designed the ``SearchPattern`` and ``SearchRewrite`` tools
and the support for the pcoq interface
(http://www-sop.inria.fr/lemme/pcoq/).

Micaela Mayero and David Delahaye introduced Field, a decision tactic
for commutative fields.

Christine Paulin changed the elimination rules for empty and singleton
propositional inductive types.

Loïc Pottier developed Fourier, a tactic solving linear inequalities on
real numbers.

Pierre Crégut developed a new, reflection-based version of the Omega
decision procedure.

Claudio Sacerdoti Coen designed an XML output for the Coq modules to be
used in the Hypertextual Electronic Library of Mathematics (HELM cf
http://www.cs.unibo.it/helm).

A library for efficient representation of finite maps using binary trees
contributed by Jean Goubault was integrated in the basic theories.

Pierre Courtieu developed a command and a tactic to reason on the
inductive structure of recursively defined functions.

Jacek Chrząszcz designed and implemented the module system of Coq whose
foundations are in Judicaël Courant’s PhD thesis.

The development was coordinated by C. Paulin.

Many discussions within the Démons team and the LogiCal project
influenced significantly the design of Coq especially with J. Courant,
J. Duprat, J. Goubault, A. Miquel, C. Marché, B. Monate and B. Werner.

Intensive users suggested improvements of the system : Y. Bertot, L.
Pottier, L. Théry, P. Zimmerman from INRIA, C. Alvarado, P. Crégut,
J.-F. Monin from France Telecom R & D.

| Orsay, May. 2002
| Hugo Herbelin & Christine Paulin
|

Details of changes in 7.0 and 7.1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Notes:

- items followed by (**) are important sources of incompatibilities
- items followed by (*) may exceptionally be sources of incompatibilities
- items followed by (+) have been introduced in version 7.0


Main novelties
^^^^^^^^^^^^^^

References are to Coq 7.1 reference manual

- New primitive let-in construct (see sections 1.2.8 and )
- Long names (see sections 2.6 and 2.7)
- New high-level tactic language (see chapter 10)
- Improved search facilities (see section 5.2)
- New extraction algorithm managing the Type level (see chapter 17)
- New rewriting tactic for arbitrary equalities (see chapter 19)
- New tactic Field to decide equalities on commutative fields (see 7.11)
- New tactic Fourier to solve linear inequalities on reals numbers (see 7.11)
- New tactics for induction/case analysis in "natural" style (see 7.7)
- Deep restructuration of the code (safer, simpler and more efficient)
- Export of theories to XML for publishing and rendering purposes
  (see http://www.cs.unibo.it/helm)


Details of changes
^^^^^^^^^^^^^^^^^^

Language: new "let-in" construction
***********************************

- New construction for local definitions (let-in) with syntax [x:=u]t (*)(+)

- Local definitions allowed in Record (a.k.a. record à la Randy Pollack)


Language: long names
********************

- Each construction has a unique absolute names built from a base
  name, the name of the module in which they are defined (Top if in
  coqtop), and possibly an arbitrary long sequence of directory (e.g.
  "Coq.Lists.PolyList.flat_map" where "Coq" means that "flat_map" is part
  of Coq standard library, "Lists" means it is defined in the Lists
  library and "PolyList" means it is in the file Polylist) (+)

- Constructions can be referred by their base name, or, in case of
  conflict, by a "qualified" name, where the base name is prefixed
  by the module name (and possibly by a directory name, and so
  on). A fully qualified name is an absolute name which always refer
  to the construction it denotes (to preserve the visibility of
  all constructions, no conflict is allowed for an absolute name) (+)

- Long names are available for modules with the possibility of using
  the directory name as a component of the module full name (with
  option -R to coqtop and coqc, or command Add LoadPath) (+)

- Improved conflict resolution strategy (the Unix PATH model),
  allowing more constructions to be referred just by their base name


Language: miscellaneous
***********************

- The names of variables for Record projections _and_ for induction principles
  (e.g. sum_ind) is now based on the first letter of their type (main
  source of incompatibility) (**)(+)

- Most typing errors have now a precise location in the source (+)

- Slightly different mechanism to solve "?" (*)(+)

- More arguments may be considered implicit at section closing (*)(+)

- Bug with identifiers ended by a number greater than 2^30 fixed (+)

- New visibility discipline for Remark, Fact and Local: Remark's and
  Fact's now survive at the end of section, but are only accessible using a
  qualified names as soon as their strength expires; Local's disappear and
  are moved into local definitions for each construction persistent at
  section closing


Language: Cases
***************

- Cases no longer considers aliases inferable from dependencies in types (*)(+)

- A redundant clause in Cases is now an error (*)


Reduction
*********

- New reduction flags "Zeta" and "Evar" in Eval Compute, for inlining of
  local definitions and instantiation of existential variables

- Delta reduction flag does not perform Zeta and Evar reduction any more (*)

- Constants declared as opaque (using Qed) can no longer become
  transparent (a constant intended to be alternatively opaque and
  transparent must be declared as transparent (using Defined)); a risk
  exists (until next Coq version) that Simpl and Hnf reduces opaque
  constants (*)


New tactics
***********

- New set of tactics to deal with types equipped with specific
  equalities (a.k.a. Setoids, e.g. nat equipped with eq_nat) [by C. Renard]

- New tactic Assert, similar to Cut but expected to be more user-friendly

- New tactic NewDestruct and NewInduction intended to replace Elim
  and Induction, Case and Destruct in a more user-friendly way (see
  restrictions in the reference manual)

- New tactic ROmega: an experimental alternative (based on reflexion) to Omega
  [by P. Crégut]

- New tactic language Ltac (see reference manual) (+)

- New versions of Tauto and Intuition, fully rewritten in the new Ltac
  language; they run faster and produce more compact proofs; Tauto is
  fully compatible but, in exchange of a better uniformity, Intuition
  is slightly weaker (then use Tauto instead) (**)(+)

- New tactic Field to decide equalities on commutative fields (as a
  special case, it works on real numbers) (+)

- New tactic Fourier to solve linear inequalities on reals numbers
  [by L. Pottier] (+)

- New tactics dedicated to real numbers: DiscrR, SplitRmult, SplitAbsolu (+)


Changes in existing tactics
***************************

- Reduction tactics in local definitions apply only to the body

- New syntax of the form "Compute in Type of H." to require a reduction on
  the types of local definitions

- Inversion, Injection, Discriminate, ... apply also on the
  quantified premises of a goal (using the "Intros until" syntax)

- Decompose has been fixed but hypotheses may get different names (*)(+)

- Tauto now manages uniformly hypotheses and conclusions of the form
  ``t=t`` which all are considered equivalent to ``True``. Especially,
  Tauto now solves goals of the form ``H : ~ t = t |- A``.

- The "Let" tactic has been renamed "LetTac" and is now based on the
  primitive "let-in" (+)

- Elim can no longer be used with an elimination schema different from
  the one defined at definition time of the inductive type. To overload
  an elimination schema, use "Elim <hyp> using <name of the new schema>"
  (*)(+)

- Simpl no longer unfolds the recursive calls of a mutually defined
  fixpoint (*)(+)

- Intro now fails if the hypothesis name already exists (*)(+)

- "Require Prolog" is no longer needed (i.e. it is available by default) (*)(+)

- Unfold now fails on a non-unfoldable identifier (*)(+)

- Unfold also applies on definitions of the local context

- AutoRewrite now deals only with the main goal and it is the purpose of
  Hint Rewrite to deal with generated subgoals (+)

- Redundant or incompatible instantiations in Apply ... with ... are now
  correctly managed (+)


Efficiency
**********

- Excessive memory uses specific to V7.0 fixed

- Sizes of .vo files vary a lot compared to V6.3 (from -30% to +300%
  depending on the developments)

- An improved reduction strategy for lazy evaluation

- A more economical mechanism to ensure logical consistency at the Type level;
  warning: this is experimental and may produce "universes" anomalies
  (please report)


Concrete syntax of constructions
********************************

- Only identifiers starting with "_" or a letter, and followed by letters,
  digits, "_" or "'" are allowed (e.g. "$" and "@" are no longer allowed) (*)

- A multiple binder like (a:A)(a,b:(P a))(Q a) is no longer parsed as
  (a:A)(a0:(P a))(b:(P a))(Q a0) but as (a:A)(a0:(P a))(b:(P a0))(Q a0) (*)(+)

- A dedicated syntax has been introduced for Reals (e.g ``3+1/x``) (+)

- Pretty-printing of Infix notations fixed. (+)


Parsing and grammar extension
*****************************

- More constraints when writing ast

  - "{...}" and the macros $LIST, $VAR, etc. now expect a metavariable
    (an identifier starting with $) (*)
  - identifiers should starts with a letter or "_" and be followed
     by letters, digits, "_" or "'" (other characters are still
     supported but it is not advised to use them) (*)(+)

- Entry "command" in "Grammar" and quotations (<<...>> stuff) is
  renamed "constr" as in "Syntax" (+)

- New syntax "[" sentence_1 ... sentence_n"]." to group sentences (useful
  for Time and to write grammar rules abbreviating several commands) (+)

- The default parser for actions in the grammar rules (and for
  patterns in the pretty-printing rules) is now the one associated with
  the grammar (i.e. vernac, tactic or constr); no need then for
  quotations as in <:vernac:<...>>; to return an "ast", the grammar
  must be explicitly typed with tag ": ast" or ": ast list", or if a
  syntax rule, by using <<...>> in the patterns (expression inside
  these angle brackets are parsed as "ast"); for grammars other than
  vernac, tactic or constr, you may explicitly type the action with
  tags ": constr", ": tactic", or ":vernac" (**)(+)

- Interpretation of names in Grammar rule is now based on long names,
  which allows to avoid problems (or sometimes tricks;) related to
  overloaded names (+)


New commands
************

- New commands "Print XML All", "Show XML Proof", ... to show or
  export theories to XML to be used with Helm's publishing and rendering
  tools (see http://www.cs.unibo.it/helm) (by Claudio Sacerdoti Coen) (+)

- New commands to manually set implicit arguments (+)

  - "Implicits ident." to activate the implicit arguments mode just for ident
  - "Implicits ident [num1 num2 ...]." to explicitly give which
     arguments have to be considered as implicit

- New SearchPattern/SearchRewrite (by Yves Bertot) (+)

- New commands "Debug on"/"Debug off" to activate/deactivate the tactic
  language debugger (+)

- New commands to map physical paths to logical paths (+)
  - Add LoadPath physical_dir as logical_dir
  - Add Rec LoadPath physical_dir as logical_dir


Changes in existing commands
****************************

- Generalization of the usage of qualified identifiers in tactics
  and commands about globals, e.g. Decompose, Eval Delta;
  Hints Unfold, Transparent, Require

- Require synchronous with Reset; Require's scope stops at Section ending (*)

- For a module indirectly loaded by a "Require" but not exported,
  the command "Import module" turns the constructions defined in the
  module accessible by their short name, and activates the Grammar,
  Syntax, Hint, ... declared in the module (+)

- The scope of the "Search" command can be restricted to some modules (+)

- Final dot in command (full stop/period) must be followed by a blank
  (newline, tabulation or whitespace) (+)

- Slight restriction of the syntax for Cbv Delta: if present, option [-myconst]
  must immediately follow the Delta keyword (*)(+)

- SearchIsos currently not supported

- Add ML Path is now implied by Add LoadPath (+)

- New names for the following commands (+)

  AddPath -> Add LoadPath
  Print LoadPath -> Print LoadPath
  DelPath -> Remove LoadPath
  AddRecPath -> Add Rec LoadPath
  Print Path -> Print Coercion Paths

  Implicit Arguments On -> Set Implicit Arguments
  Implicit Arguments Off -> Unset Implicit Arguments

  Begin Silent -> Set Silent
  End Silent -> Unset Silent.


Tools
*****

- coqtop (+)

  - Two executables: coqtop.byte and coqtop.opt (if supported by the platform)
  - coqtop is a link to the more efficient executable (coqtop.opt if present)
  - option -full is obsolete (+)

- do_Makefile renamed into coq_makefile (+)

- New option -R to coqtop and coqc to map a physical directory to a logical
  one (+)

- coqc no longer needs to create a temporary file

- No more warning if no initialization file .coqrc exists


Extraction
**********

- New algorithm for extraction able to deal with "Type" (+)
  (by J.-C. Filliâtre and P. Letouzey)


Standard library
****************

- New library on maps on integers (IntMap, contributed by Jean Goubault)

- New lemmas about integer numbers [ZArith]

- New lemmas and a "natural" syntax for reals [Reals] (+)

- Exc/Error/Value renamed into Option/Some/None (*)


New user contributions
**********************

- Constructive complex analysis and the Fundamental Theorem of Algebra [FTA]
  (Herman Geuvers, Freek Wiedijk, Jan Zwanenburg, Randy Pollack,
  Henk Barendregt, Nijmegen)

- A new axiomatization of ZFC set theory [Functions_in_ZFC]
  (C. Simpson, Sophia-Antipolis)

- Basic notions of graph theory [GRAPHS-BASICS] (Jean Duprat, Lyon)

- A library for floating-point numbers [Float] (Laurent Théry, Sylvie Boldo,
  Sophia-Antipolis)

- Formalisation of CTL and TCTL temporal logic [CtlTctl] (Carlos
  Daniel Luna,Montevideo)

- Specification and verification of the Railroad Crossing Problem
  in CTL and TCTL [RailroadCrossing] (Carlos Daniel Luna,Montevideo)

- P-automaton and the ABR algorithm [PAutomata]
  (Christine Paulin, Emmanuel Freund, Orsay)

- Semantics of a subset of the C language [MiniC]
  (Eduardo Giménez, Emmanuel Ledinot, Suresnes)

- Correctness proofs of the following imperative algorithms:
  Bresenham line drawing algorithm [Bresenham], Marché's minimal edition
  distance algorithm [Diff] (Jean-Christophe Filliâtre, Orsay)

- Correctness proofs of Buchberger's algorithm [Buchberger] and RSA
  cryptographic algorithm [Rsa] (Laurent Théry, Sophia-Antipolis)

- Correctness proof of Stalmarck tautology checker algorithm
  [Stalmarck] (Laurent Théry, Pierre Letouzey, Sophia-Antipolis)


Details of changes in 7.2
~~~~~~~~~~~~~~~~~~~~~~~~~

Language

- Automatic insertion of patterns for local definitions in the type of
  the constructors of an inductive types (for compatibility with V6.3
  let-in style)
- Coercions allowed in Cases patterns
- New declaration "Canonical Structure id = t : I" to help resolution of
  equations of the form (proj ?)=a; if proj(e)=a then a is canonically
  equipped with the remaining fields in e, i.e. ? is instantiated by e

Tactics

- New tactic "ClearBody H" to clear the body of definitions in local context
- New tactic "Assert H := c" for forward reasoning
- Slight improvement in naming strategy for NewInduction/NewDestruct
- Intuition/Tauto do not perform useless unfolding and work up to conversion

Extraction (details in plugins/extraction/CHANGES or documentation)

- Syntax changes: there are no more options inside the extraction commands.
  New commands for customization and options have been introduced instead.
- More optimizations on extracted code.
- Extraction tests are now embedded in 14 user contributions.

Standard library

- In [Relations], Rstar.v and Newman.v now axiom-free.
- In [Sets], Integers.v now based on nat
- In [Arith], more lemmas in Min.v, new file Max.v, tail-recursive
  plus and mult added to Plus.v and Mult.v respectively
- New directory [Sorting] with a proof of heapsort (dragged from 6.3.1 lib)
- In [Reals], more lemmas in Rbase.v, new lemmas on square, square root and
  trigonometric functions (R_sqr.v - Rtrigo.v); a complementary approach
  and new theorems about continuity and derivability in Ranalysis.v;  some
  properties in plane geometry such as translation, rotation or similarity
  in Rgeom.v; finite sums and Chasles property in Rsigma.v

Bugs

- Confusion between implicit args of locals and globals of same base name fixed
- Various incompatibilities wrt inference of "?" in V6.3.1 fixed
- Implicits in infix section variables bug fixed
- Known coercions bugs fixed

- Apply "universe anomaly" bug fixed
- NatRing now working
- "Discriminate 1", "Injection 1", "Simplify_eq 1" now working
- NewInduction bugs with let-in and recursively dependent hypotheses fixed
- Syntax [x:=t:T]u now allowed as mentioned in documentation

- Bug with recursive inductive types involving let-in fixed
- Known pattern-matching bugs fixed
- Known Cases elimination predicate bugs fixed
- Improved errors messages for pattern-matching and projections
- Better error messages for ill-typed Cases expressions

Incompatibilities

- New naming strategy for NewInduction/NewDestruct may affect 7.1 compatibility
- Extra parentheses may exceptionally be needed in tactic definitions.
- Coq extensions written in OCaml need to be updated (see dev/changements.txt
  for a description of the main changes in the interface files of V7.2)
- New behavior of Intuition/Tauto may exceptionally lead to incompatibilities


Details of changes in 7.3
~~~~~~~~~~~~~~~~~~~~~~~~~

Language

- Slightly improved compilation of pattern-matching (slight source of
  incompatibilities)
- Record's now accept anonymous fields "_" which does not build projections
- Changes in the allowed elimination sorts for certain class of inductive
  definitions : an inductive definition without constructors
  of Sort Prop can be eliminated on sorts Set and Type A "singleton"
  inductive definition (one constructor with arguments in the sort Prop
  like conjunction of two propositions or equality) can be eliminated
  directly on sort Type (In V7.2, only the sorts Prop and Set were allowed)

Tactics

- New tactic "Rename x into y" for renaming hypotheses
- New tactics "Pose x:=u" and "Pose u" to add definitions to local context
- Pattern now working on partially applied subterms
- Ring no longer applies irreversible congruence laws of mult but
  better applies congruence laws of plus (slight source of incompatibilities).
- Field now accepts terms to be simplified as arguments (as for Ring). This
  extension has been also implemented using the toplevel tactic language.
- Intuition does no longer unfold constants except "<->" and "~". It
  can be parameterized by a tactic. It also can introduce dependent
  product if needed (source of incompatibilities)
- "Match Context" now matching more recent hypotheses first and failing only
  on user errors and Fail tactic (possible source of incompatibilities)
- Tactic Definition's without arguments now allowed in Coq states
- Better simplification and discrimination made by Inversion (source
  of incompatibilities)

Bugs

- "Intros H" now working like "Intro H" trying first to reduce if not a product
- Forward dependencies in Cases now taken into account
- Known bugs related to Inversion and let-in's fixed
- Bug unexpected Delta with let-in now fixed

Extraction (details in plugins/extraction/CHANGES or documentation)

- Signatures of extracted terms are now mostly expunged from dummy arguments.
- Haskell extraction is now operational (tested & debugged).

Standard library

- Some additions in [ZArith]: three files (Zcomplements.v, Zpower.v
  and Zlogarithms.v) moved from plugins/omega in order to be more
  visible, one Zsgn function, more induction principles (Wf_Z.v and
  tail of Zcomplements.v), one more general Euclid theorem
- Peano_dec.v and Compare_dec.v now part of Arith.v

Tools

- new option -dump-glob to coqtop to dump globalizations (to be used by the
  new documentation tool coqdoc; see http://www.lri.fr/~filliatr/coqdoc)

User Contributions

- CongruenceClosure (congruence closure decision procedure)
  [Pierre Corbineau, ENS Cachan]
- MapleMode (an interface to embed Maple simplification procedures over
  rational fractions in Coq)
  [David Delahaye, Micaela Mayero, Chalmers University]
- Presburger: A formalization of Presburger's algorithm
  [Laurent Thery, INRIA Sophia Antipolis]
- Chinese has been rewritten using Z from ZArith as datatype
  ZChinese is the new version, Chinese the obsolete one
  [Pierre Letouzey, LRI Orsay]

Incompatibilities

- Ring: exceptional incompatibilities (1 above 650 in submitted user
  contribs, leading to a simplification)
- Intuition: does not unfold any definition except "<->" and "~"
- Cases: removal of some extra Cases in configurations of the form
  "Cases ... of C _ => ... | _ D => ..."  (effects on 2 definitions of
  submitted user contributions necessitating the removal of now superfluous
  proof steps in 3 different proofs)
- Match Context, in case of incompatibilities because of a now non
  trapped error (e.g. Not_found or Failure), use instead tactic Fail
  to force Match Context trying the next clause
- Inversion: better simplification and discrimination may occasionally
  lead to less subgoals and/or hypotheses and different naming of hypotheses
- Unification done by Apply/Elim has been changed and may exceptionally lead
  to incompatible instantiations
- Peano_dec.v and Compare_dec.v parts of Arith.v make Auto more
  powerful if these files were not already required (1 occurrence of
  this in submitted user contribs)


Changes in 7.3.1
^^^^^^^^^^^^^^^^

Bug fixes

  - Corrupted Field tactic and Match Context tactic construction fixed
  - Checking of names already existing in Assert added (#1386)
  - Invalid argument bug in Exact tactic solved (#1387)
  - Colliding bound names bug fixed (#1412)
  - Wrong non-recursivity test for Record fixed (#1394)
  - Out of memory/seg fault bug related to parametric inductive fixed (#1404)
  - Setoid_replace/Setoid_rewrite bug wrt "==" fixed

Misc

  - Ocaml version >= 3.06 is needed to compile Coq from sources
  - Simplification of fresh names creation strategy for Assert, Pose and
    LetTac (#1402)


Details of changes in 7.4
~~~~~~~~~~~~~~~~~~~~~~~~~

Symbolic notations

- Introduction of a notion of scope gathering notations in a consistent set;
  a notation sets has been developed for nat, Z and R (undocumented)
- New command "Notation" for declaring notations simultaneously for
  parsing and printing (see chap 10 of the reference manual)
- Declarations with only implicit arguments now handled (e.g. the
  argument of nil can be set implicit; use !nil to refer to nil
  without arguments)
- "Print Scope sc" and "Locate ntn" allows to know to what expression a
  notation is bound
- New defensive strategy for printing or not implicit arguments to ensure
  re-type-checkability of the printed term
- In Grammar command, the only predefined non-terminal entries are ident,
  global, constr and pattern (e.g. nvar, numarg disappears); the only
  allowed grammar types are constr and pattern; ast and ast list are no
  longer supported; some incompatibilities in Grammar: when a syntax is a
  initial segment of an other one,  Grammar does not work, use Notation

Library

- Lemmas in Set from Compare_dec.v (le_lt_dec, ...) and Wf_nat.v
  (lt_wf_rec, ...) are now transparent. This may be source of
  incompatibilities.
- Syntactic Definitions Fst, Snd, Ex, All, Ex2, AllT, ExT, ExT2,
  ProjS1, ProjS2, Error, Value and Except are turned to
  notations. They now must be applied (incompatibilities only in
  unrealistic cases).
- More efficient versions of Zmult and times (30% faster)
- Reals: the library is now divided in 6 parts (Rbase, Rfunctions,
  SeqSeries, Rtrigo, Ranalysis, Integration). New tactics: Sup and
  RCompute. See Reals.v for details.

Modules

- Beta version, see doc chap 2.5 for commands and chap 5 for theory

Language

- Inductive definitions now accept ">" in constructor types to declare
  the corresponding constructor as a coercion.
- Idem for assumptions declarations and constants when the type is mentioned.
- The "Coercion" and "Canonical Structure" keywords now accept the
  same syntax as "Definition", i.e. "hyps :=c (:t)?" or "hyps :t".
- Theorem-like declaration now accepts the syntax "Theorem thm [x:t;...] : u".
- Remark's and Fact's now definitively behave as Theorem and Lemma: when
  sections are closed, the full name of a Remark or a Fact has no longer a
  section part (source of incompatibilities)
- Opaque Local's (i.e. built by tactics and ended by Qed), do not
  survive section closing any longer; as a side-effect, Opaque Local's
  now appear in the local context of proofs; their body is hidden
  though (source of incompatibilities); use one of Remark/Fact/Lemma/Theorem
  instead to simulate the old behavior of Local (the section part of
  the name is not kept though)

ML tactics and commands

- "Grammar tactic" and "Grammar vernac" of type "ast" are no longer
  supported (only "Grammar tactic simple_tactic" of type "tactic"
  remains available).
- Concrete syntax for ML written commands and tactics is
  now declared at ML level using camlp4 macros TACTIC EXTEND et VERNAC
  COMMAND EXTEND.
- "Check n c" now "n:Check c", "Eval n ..." now "n:Eval ..."
- ``Proof with T`` (no documentation)
-  SearchAbout id - prints all theorems which contain id in their type

Tactic definitions

- Static globalisation of identifiers and global references (source of
  incompatibilities, especially, Recursive keyword is required for
  mutually recursive definitions).
- New evaluation semantics: no more partial evaluation at definition time;
  evaluation of all Tactic/Meta Definition, even producing terms, expect
  a proof context to be evaluated (especially "()" is no longer needed).
- Debugger now shows the nesting level and the reasons of failure

Tactics

- Equality tactics (Rewrite, Reflexivity, Symmetry, Transitivity) now
  understand JM equality
- Simpl and Change now apply to subterms also
- "Simpl f" reduces subterms whose :term:`head constant` is f
- Double Induction now referring to hypotheses like "Intros until"
- "Inversion" now applies also on quantified hypotheses (naming as
  for Intros until)
- NewDestruct now accepts terms with missing hypotheses
- NewDestruct and NewInduction now accept user-provided elimination scheme
- NewDestruct and NewInduction now accept user-provided introduction names
- Omega could solve goals such as ``~x<y |- x>=y`` but failed when the
  hypothesis was unfolded to ``x < y -> False``. This is fixed. In addition,
  it can also recognize 'False' in the hypothesis and use it to solve the
  goal.
- Coercions now handled in "with" bindings
- "Subst x" replaces all occurrences of x by t in the goal and hypotheses
  when an hypothesis x=t or x:=t or t=x exists
- Fresh names for Assert and Pose now based on collision-avoiding
  Intro naming strategy (exceptional source of incompatibilities)
- LinearIntuition (no documentation)
- Unfold expects a correct evaluable argument
- Clear expects existing hypotheses

Extraction (See details in plugins/extraction/CHANGES and README):

- An experimental Scheme extraction is provided.
- Concerning OCaml, extracted code is now ensured to always type check,
  thanks to automatic inserting of Obj.magic.
- Experimental extraction of Coq new modules to Ocaml modules.

Proof rendering in natural language

- Export of theories to XML for publishing and rendering purposes now
  includes proof-trees (see http://www.cs.unibo.it/helm)

Miscellaneous

- Printing Coercion now used through the standard keywords Set/Add, Test, Print
- "Print Term id" is an alias for "Print id"
- New switch "Unset/Set Printing Symbols" to control printing of
  symbolic notations
- Two new variants of implicit arguments are available

  + ``Unset``/``Set Contextual Implicits`` tells to consider implicit also the
    arguments inferable from the context (e.g. for nil or refl_eq)
  + ``Unset``/``Set Strict Implicits`` tells to consider implicit only the
    arguments that are inferable in any case (i.e. arguments that occurs
    as argument of rigid constants in the type of the remaining arguments;
    e.g. the witness of an existential is not strict since it can vanish when
    applied to a predicate which does not use its argument)

Incompatibilities

- "Grammar tactic ... : ast" and "Grammar vernac ... : ast" are no
  longer supported, use TACTIC EXTEND and VERNAC COMMAND EXTEND on the
  ML-side instead
- Transparency of le_lt_dec and co (leads to some simplification in
  proofs; in some cases, incompatibilites is solved by declaring locally
  opaque the relevant constant)
- Opaque Local do not now survive section closing (rename them into
  Remark/Lemma/... to get them still surviving the sections; this
  renaming allows also to solve incompatibilites related to now
  forbidden calls to the tactic Clear)
- Remark and Fact have no longer (very) long names (use Local instead in case
  of name conflict)

Bugs

- Improved localisation of errors in Syntactic Definitions
- Induction principle creation failure in presence of let-in fixed (#1459)
- Inversion bugs fixed (#1427 and #1437)
- Omega bug related to Set fixed (#1384)
- Type-checking inefficiency of nested destructuring let-in fixed (#1435)
- Improved handling of let-in during holes resolution phase (#1460)

Efficiency

- Implementation of a memory sharing strategy reducing memory
  requirements by an average ratio of 3.
