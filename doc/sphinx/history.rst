--------------------
Early history of Coq
--------------------

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

The logical language used by |Coq| is a variety of type theory, called the
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
advantage of special hardware, debuggers, and the like. We hope that |Coq|
can be of use to researchers interested in experimenting with this new
methodology.

.. [#years] At the time of writting, i.e. 1995.

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
Doligez by D. de Rauglaudre (Version 5.7) in 1992. A new version of |Coq|
was then coordinated by C. Murthy, with new tools designed by C. Parent
to prove properties of ML programs (this methodology is dual to program
extraction) and a new user-interaction loop. This system (Version 5.8)
was released in May 1993. A Centaur interface CTCoq was then developed
by Y. Bertot from the Croap project from INRIA-Sophia-Antipolis.

In parallel, G. Dowek and H. Herbelin developed a new proof engine,
allowing the general manipulation of existential variables consistently
with dependent types in an experimental version of |Coq| (V5.9).

The version V5.10 of |Coq| is based on a generic system for manipulating
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

This software is a prototype type-checker for a higher-order logical
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

Thierry Coquand held a post-doctoral position in Cambrige University
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
developped on the VAX central computer of our lab, was transferred on
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
final type-checking pass. This induced a certain puzzlement in early
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
with complete documentation and a library of users' developements. The
use of the RCS revision control system, and systematic ChangeLog
files, allow a more precise tracking of the software developments.

| September 2015 +
| Thierry Coquand, Gérard Huet and Christine Paulin-Mohring.
|

Versions 6
----------

Version 6.1
~~~~~~~~~~~

The present version 6.1 of |Coq| is based on the V5.10 architecture. It
was ported to the new language Objective Caml by Bruno Barras. The
underlying framework has slightly changed and allows more conversions
between sorts.

The new version provides powerful tools for easier developments.

Cristina Cornes designed an extension of the |Coq| syntax to allow
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
integrated to the |Coq| system by Hugo Herbelin.

Samuel Boutin designed a tactic for simplification of commutative rings
using a canonical set of rewriting rules and equality modulo
associativity and commutativity.

Finally the organisation of the |Coq| distribution has been supervised by
Jean-Christophe Filliâtre with the help of Judicaël Courant and Bruno
Barras.

| Lyon, Nov. 18th 1996
| Christine Paulin
|

Version 6.2
~~~~~~~~~~~

In version 6.2 of |Coq|, the parsing is done using camlp4, a preprocessor
and pretty-printer for CAML designed by Daniel de Rauglaudre at INRIA.
Daniel de Rauglaudre made the first adaptation of |Coq| for camlp4, this
work was continued by Bruno Barras who also changed the structure of |Coq|
abstract syntax trees and the primitives to manipulate them. The result
of these changes is a faster parsing procedure with greatly improved
syntax-error messages. The user-interface to introduce grammar or
pretty-printing rules has also changed.

Eduardo Giménez redesigned the internal tactic libraries, giving uniform
names to Caml functions corresponding to |Coq| tactic names.

Bruno Barras wrote new, more efficient reduction functions.

Hugo Herbelin introduced more uniform notations in the |Coq| specification
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

Henri Laulhère produced the |Coq| distribution for the Windows
environment.

Finally, Hugo Herbelin was the main coordinator of the |Coq| documentation
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

The version V7 is a new implementation started in September 1999 by
Jean-Christophe Filliâtre. This is a major revision with respect to the
internal architecture of the system. The |Coq| version 7.0 was distributed
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
contributed to the simplification of |Coq| internal structures and the
optimisation of the system. He added basic tactics for forward reasoning
and coercions in patterns.

David Delahaye introduced a new language for tactics. General tactics
using pattern matching on goals and context can directly be written from
the |Coq| toplevel. He also provided primitives for the design of
user-defined tactics in Caml.

Micaela Mayero contributed the library on real numbers. Olivier
Desmettre extended this library with axiomatic trigonometric functions,
square, square roots, finite sums, Chasles property and basic plane
geometry.

Jean-Christophe Filliâtre and Pierre Letouzey redesigned a new
extraction procedure from |Coq| terms to Caml or Haskell programs. This
new extraction procedure, unlike the one implemented in previous version
of |Coq| is able to handle all terms in the Calculus of Inductive
Constructions, even involving universes and strong elimination. P.
Letouzey adapted user contributions to extract ML programs when it was
sensible. Jean-Christophe Filliâtre wrote ``coqdoc``, a documentation
tool for |Coq| libraries usable from version 7.2.

Bruno Barras improved the efficiency of the reduction algorithm and the
confidence level in the correctness of |Coq| critical type checking
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

Claudio Sacerdoti Coen designed an XML output for the |Coq| modules to be
used in the Hypertextual Electronic Library of Mathematics (HELM cf
http://www.cs.unibo.it/helm).

A library for efficient representation of finite maps using binary trees
contributed by Jean Goubault was integrated in the basic theories.

Pierre Courtieu developed a command and a tactic to reason on the
inductive structure of recursively defined functions.

Jacek Chrząszcz designed and implemented the module system of |Coq| whose
foundations are in Judicaël Courant’s PhD thesis.

The development was coordinated by C. Paulin.

Many discussions within the Démons team and the LogiCal project
influenced significantly the design of |Coq| especially with J. Courant,
J. Duprat, J. Goubault, A. Miquel, C. Marché, B. Monate and B. Werner.

Intensive users suggested improvements of the system : Y. Bertot, L.
Pottier, L. Théry, P. Zimmerman from INRIA, C. Alvarado, P. Crégut,
J.-F. Monin from France Telecom R & D.

| Orsay, May. 2002
| Hugo Herbelin & Christine Paulin
|
