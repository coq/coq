-------
Credits
-------

Coq is a proof assistant for higher-order logic, allowing the
development of computer programs consistent with their formal
specification. It is the result of about ten years of research of the
Coq project. We shall briefly survey here three main aspects: the
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
:math:`\lambda`-calculus occurred with Church’s *Simple Theory of
Types*. The :math:`\lambda`-calculus notation, originally used for
expressing functionality, could also be used as an encoding of natural
deduction proofs. This Curry-Howard isomorphism was used by N. de Bruijn
in the *Automath* project, the first full-scale attempt to develop and
mechanically verify mathematical proofs. This effort culminated with
Jutting’s verification of Landau’s *Grundlagen* in the 1970’s.
Exploiting this Curry-Howard isomorphism, notable achievements in proof
theory saw the emergence of two type-theoretic frameworks; the first
one, Martin-Löf’s *Intuitionistic Theory of Types*, attempts a new
foundation of mathematics on constructive principles. The second one,
Girard’s polymorphic :math:`\lambda`-calculus :math:`F_\omega`, is a
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

A first implementation of CoC was started in 1984 by G. Huet and T.
Coquand. Its implementation language was CAML, a functional programming
language from the ML family designed at INRIA in Rocquencourt. The core
of this system was a proof-checker for CoC seen as a typed
:math:`\lambda`-calculus, called the *Constructive Engine*. This engine
was operated through a high-level notation permitting the declaration of
axioms and parameters, the definition of mathematical types and objects,
and the explicit construction of proof objects encoded as
:math:`\lambda`-terms. A section mechanism, designed and implemented by
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

Credits: addendum for version 6.1
---------------------------------

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

Credits: addendum for version 6.2
---------------------------------

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

Credits: addendum for version 6.3
---------------------------------

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

Credits: versions 7
-------------------

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

Credits: version 8.0
--------------------

Coq version 8 is a major revision of the |Coq| proof assistant. First, the
underlying logic is slightly different. The so-called *impredicativity*
of the sort Set has been dropped. The main reason is that it is
inconsistent with the principle of description which is quite a useful
principle for formalizing mathematics within classical logic. Moreover,
even in an constructive setting, the impredicativity of Set does not add
so much in practice and is even subject of criticism from a large part
of the intuitionistic mathematician community. Nevertheless, the
impredicativity of Set remains optional for users interested in
investigating mathematical developments which rely on it.

Secondly, the concrete syntax of terms has been completely revised. The
main motivations were

-  a more uniform, purified style: all constructions are now lowercase,
   with a functional programming perfume (e.g. abstraction is now
   written fun), and more directly accessible to the novice (e.g.
   dependent product is now written forall and allows omission of
   types). Also, parentheses are no longer mandatory for function
   application.

-  extensibility: some standard notations (e.g. “<” and “>”) were
   incompatible with the previous syntax. Now all standard arithmetic
   notations (=, +, \*, /, <, <=, ... and more) are directly part of the
   syntax.

Together with the revision of the concrete syntax, a new mechanism of
*interpretation scopes* permits to reuse the same symbols (typically +,
-, \*, /, <, <=) in various mathematical theories without any
ambiguities for |Coq|, leading to a largely improved readability of |Coq|
scripts. New commands to easily add new symbols are also provided.

Coming with the new syntax of terms, a slight reform of the tactic
language and of the language of commands has been carried out. The
purpose here is a better uniformity making the tactics and commands
easier to use and to remember.

Thirdly, a restructuring and uniformization of the standard library of
Coq has been performed. There is now just one Leibniz equality usable
for all the different kinds of |Coq| objects. Also, the set of real
numbers now lies at the same level as the sets of natural and integer
numbers. Finally, the names of the standard properties of numbers now
follow a standard pattern and the symbolic notations for the standard
definitions as well.

The fourth point is the release of |CoqIDE|, a new graphical gtk2-based
interface fully integrated with |Coq|. Close in style to the Proof General
Emacs interface, it is faster and its integration with |Coq| makes
interactive developments more friendly. All mathematical Unicode symbols
are usable within |CoqIDE|.

Finally, the module system of |Coq| completes the picture of |Coq| version
8.0. Though released with an experimental status in the previous version
7.4, it should be considered as a salient feature of the new version.

Besides, |Coq| comes with its load of novelties and improvements: new or
improved tactics (including a new tactic for solving first-order
statements), new management commands, extended libraries.

Bruno Barras and Hugo Herbelin have been the main contributors of the
reflection and the implementation of the new syntax. The smart automatic
translator from old to new syntax released with |Coq| is also their work
with contributions by Olivier Desmettre.

Hugo Herbelin is the main designer and implementer of the notion of
interpretation scopes and of the commands for easily adding new
notations.

Hugo Herbelin is the main implementer of the restructured standard library.

Pierre Corbineau is the main designer and implementer of the new tactic
for solving first-order statements in presence of inductive types. He is
also the maintainer of the non-domain specific automation tactics.

Benjamin Monate is the developer of the |CoqIDE| graphical interface with
contributions by Jean-Christophe Filliâtre, Pierre Letouzey, Claude
Marché and Bruno Barras.

Claude Marché coordinated the edition of the Reference Manual for |Coq|
V8.0.

Pierre Letouzey and Jacek Chrząszcz respectively maintained the
extraction tool and module system of |Coq|.

Jean-Christophe Filliâtre, Pierre Letouzey, Hugo Herbelin and other
contributors from Sophia-Antipolis and Nijmegen participated in
extending the library.

Julien Narboux built a NSIS-based automatic |Coq| installation tool for
the Windows platform.

Hugo Herbelin and Christine Paulin coordinated the development which was
under the responsibility of Christine Paulin.

| Palaiseau & Orsay, Apr. 2004
| Hugo Herbelin & Christine Paulin
| (updated Apr. 2006)
|

Credits: version 8.1
--------------------

Coq version 8.1 adds various new functionalities.

Benjamin Grégoire implemented an alternative algorithm to check the
convertibility of terms in the |Coq| type checker. This alternative
algorithm works by compilation to an efficient bytecode that is
interpreted in an abstract machine similar to Xavier Leroy’s ZINC
machine. Convertibility is performed by comparing the normal forms. This
alternative algorithm is specifically interesting for proofs by
reflection. More generally, it is convenient in case of intensive
computations.

Christine Paulin implemented an extension of inductive types allowing
recursively non uniform parameters. Hugo Herbelin implemented
sort-polymorphism for inductive types (now called template polymorphism).

Claudio Sacerdoti Coen improved the tactics for rewriting on arbitrary
compatible equivalence relations. He also generalized rewriting to
arbitrary transition systems.

Claudio Sacerdoti Coen added new features to the module system.

Benjamin Grégoire, Assia Mahboubi and Bruno Barras developed a new, more
efficient and more general simplification algorithm for rings and
semirings.

Laurent Théry and Bruno Barras developed a new, significantly more
efficient simplification algorithm for fields.

Hugo Herbelin, Pierre Letouzey, Julien Forest, Julien Narboux and
Claudio Sacerdoti Coen added new tactic features.

Hugo Herbelin implemented matching on disjunctive patterns.

New mechanisms made easier the communication between |Coq| and external
provers. Nicolas Ayache and Jean-Christophe Filliâtre implemented
connections with the provers cvcl, Simplify and zenon. Hugo Herbelin
implemented an experimental protocol for calling external tools from the
tactic language.

Matthieu Sozeau developed Russell, an experimental language to specify
the behavior of programs with subtypes.

A mechanism to automatically use some specific tactic to solve
unresolved implicit has been implemented by Hugo Herbelin.

Laurent Théry’s contribution on strings and Pierre Letouzey and
Jean-Christophe Filliâtre’s contribution on finite maps have been
integrated to the |Coq| standard library. Pierre Letouzey developed a
library about finite sets “à la Objective Caml”. With Jean-Marc Notin,
he extended the library on lists. Pierre Letouzey’s contribution on
rational numbers has been integrated and extended.

Pierre Corbineau extended his tactic for solving first-order statements.
He wrote a reflection-based intuitionistic tautology solver.

Pierre Courtieu, Julien Forest and Yves Bertot added extra support to
reason on the inductive structure of recursively defined functions.

Jean-Marc Notin significantly contributed to the general maintenance of
the system. He also took care of ``coqdoc``.

Pierre Castéran contributed to the documentation of (co-)inductive types
and suggested improvements to the libraries.

Pierre Corbineau implemented a declarative mathematical proof language,
usable in combination with the tactic-based style of proof.

Finally, many users suggested improvements of the system through the
Coq-Club mailing list and bug-tracker systems, especially user groups
from INRIA Rocquencourt, Radboud University, University of Pennsylvania
and Yale University.

| Palaiseau, July 2006
| Hugo Herbelin
|

Credits: version 8.2
--------------------

Coq version 8.2 adds new features, new libraries and improves on many
various aspects.

Regarding the language of |Coq|, the main novelty is the introduction by
Matthieu Sozeau of a package of commands providing Haskell-style typeclasses.
Typeclasses, which come with a few convenient features such as
type-based resolution of implicit arguments, play a new landmark role
in the architecture of |Coq| with respect to automation. For
instance, thanks to typeclass support, Matthieu Sozeau could
implement a new resolution-based version of the tactics dedicated to
rewriting on arbitrary transitive relations.

Another major improvement of |Coq| 8.2 is the evolution of the arithmetic
libraries and of the tools associated to them. Benjamin Grégoire and
Laurent Théry contributed a modular library for building arbitrarily
large integers from bounded integers while Evgeny Makarov contributed a
modular library of abstract natural and integer arithmetic together
with a few convenient tactics. On his side, Pierre Letouzey made
numerous extensions to the arithmetic libraries on :math:`\mathbb{Z}`
and :math:`\mathbb{Q}`, including extra support for automation in
presence of various number-theory concepts.

Frédéric Besson contributed a reflective tactic based on Krivine-Stengle
Positivstellensatz (the easy way) for validating provability of systems
of inequalities. The platform is flexible enough to support the
validation of any algorithm able to produce a “certificate” for the
Positivstellensatz and this covers the case of Fourier-Motzkin (for
linear systems in :math:`\mathbb{Q}` and :math:`\mathbb{R}`),
Fourier-Motzkin with cutting planes (for linear systems in
:math:`\mathbb{Z}`) and sum-of-squares (for non-linear systems). Evgeny
Makarov made the platform generic over arbitrary ordered rings.

Arnaud Spiwack developed a library of 31-bits machine integers and,
relying on Benjamin Grégoire and Laurent Théry’s library, delivered a
library of unbounded integers in base :math:`2^{31}`. As importantly, he
developed a notion of “retro-knowledge” so as to safely extend the
kernel-located bytecode-based efficient evaluation algorithm of |Coq|
version 8.1 to use 31-bits machine arithmetic for efficiently computing
with the library of integers he developed.

Beside the libraries, various improvements were contributed to provide a more
comfortable end-user language and more expressive tactic language. Hugo
Herbelin and Matthieu Sozeau improved the pattern matching compilation
algorithm (detection of impossible clauses in pattern matching,
automatic inference of the return type). Hugo Herbelin, Pierre Letouzey
and Matthieu Sozeau contributed various new convenient syntactic
constructs and new tactics or tactic features: more inference of
redundant information, better unification, better support for proof or
definition by fixpoint, more expressive rewriting tactics, better
support for meta-variables, more convenient notations...

Élie Soubiran improved the module system, adding new features (such as
an “include” command) and making it more flexible and more general. He
and Pierre Letouzey improved the support for modules in the extraction
mechanism.

Matthieu Sozeau extended the Russell language, ending in an convenient
way to write programs of given specifications, Pierre Corbineau extended
the Mathematical Proof Language and the automation tools that
accompany it, Pierre Letouzey supervised and extended various parts of the
standard library, Stéphane Glondu contributed a few tactics and
improvements, Jean-Marc Notin provided help in debugging, general
maintenance and coqdoc support, Vincent Siles contributed extensions of
the Scheme command and of injection.

Bruno Barras implemented the ``coqchk`` tool: this is a stand-alone
type checker that can be used to certify .vo files. Especially, as this
verifier runs in a separate process, it is granted not to be “hijacked”
by virtually malicious extensions added to |Coq|.

Yves Bertot, Jean-Christophe Filliâtre, Pierre Courtieu and Julien
Forest acted as maintainers of features they implemented in previous
versions of |Coq|.

Julien Narboux contributed to |CoqIDE|. Nicolas Tabareau made the
adaptation of the interface of the old “setoid rewrite” tactic to the
new version. Lionel Mamane worked on the interaction between |Coq| and its
external interfaces. With Samuel Mimram, he also helped making |Coq|
compatible with recent software tools. Russell O’Connor, Cezary
Kaliszyk, Milad Niqui contributed to improve the libraries of integers,
rational, and real numbers. We also thank many users and partners for
suggestions and feedback, in particular Pierre Castéran and Arthur
Charguéraud, the INRIA Marelle team, Georges Gonthier and the
INRIA-Microsoft Mathematical Components team, the Foundations group at
Radboud university in Nijmegen, reporters of bugs and participants to
the Coq-Club mailing list.

| Palaiseau, June 2008
| Hugo Herbelin
|

Credits: version 8.3
--------------------

Coq version 8.3 is before all a transition version with refinements or
extensions of the existing features and libraries and a new tactic nsatz
based on Hilbert’s Nullstellensatz for deciding systems of equations
over rings.

With respect to libraries, the main evolutions are due to Pierre
Letouzey with a rewriting of the library of finite sets FSets and a new
round of evolutions in the modular development of arithmetic (library
Numbers). The reason for making FSets evolve is that the computational
and logical contents were quite intertwined in the original
implementation, leading in some cases to longer computations than
expected and this problem is solved in the new MSets implementation. As
for the modular arithmetic library, it was only dealing with the basic
arithmetic operators in the former version and its current extension
adds the standard theory of the division, min and max functions, all
made available for free to any implementation of :math:`\mathbb{N}`,
:math:`\mathbb{Z}` or :math:`\mathbb{Z}/n\mathbb{Z}`.

The main other evolutions of the library are due to Hugo Herbelin who
made a revision of the sorting library (including a certified
merge-sort) and to Guillaume Melquiond who slightly revised and cleaned
up the library of reals.

The module system evolved significantly. Besides the resolution of some
efficiency issues and a more flexible construction of module types, Élie
Soubiran brought a new model of name equivalence, the
:math:`\Delta`-equivalence, which respects as much as possible the names
given by the users. He also designed with Pierre Letouzey a new,
convenient operator ``<+`` for nesting functor application that
provides a light notation for inheriting the properties of cascading
modules.

The new tactic nsatz is due to Loïc Pottier. It works by computing
Gröbner bases. Regarding the existing tactics, various improvements have
been done by Matthieu Sozeau, Hugo Herbelin and Pierre Letouzey.

Matthieu Sozeau extended and refined the typeclasses and Program
features (the Russell language). Pierre Letouzey maintained and improved
the extraction mechanism. Bruno Barras and Élie Soubiran maintained the
Coq checker, Julien Forest maintained the Function mechanism for
reasoning over recursively defined functions. Matthieu Sozeau, Hugo
Herbelin and Jean-Marc Notin maintained coqdoc. Frédéric Besson
maintained the Micromega platform for deciding systems of inequalities.
Pierre Courtieu maintained the support for the Proof General Emacs
interface. Claude Marché maintained the plugin for calling external
provers (dp). Yves Bertot made some improvements to the libraries of
lists and integers. Matthias Puech improved the search functions.
Guillaume Melquiond usefully contributed here and there. Yann
Régis-Gianas grounded the support for Unicode on a more standard and
more robust basis.

Though invisible from outside, Arnaud Spiwack improved the general
process of management of existential variables. Pierre Letouzey and
Stéphane Glondu improved the compilation scheme of the |Coq| archive.
Vincent Gross provided support to |CoqIDE|. Jean-Marc Notin provided
support for benchmarking and archiving.

Many users helped by reporting problems, providing patches, suggesting
improvements or making useful comments, either on the bug tracker or on
the Coq-Club mailing list. This includes but not exhaustively Cédric
Auger, Arthur Charguéraud, François Garillot, Georges Gonthier, Robin
Green, Stéphane Lescuyer, Eelis van der Weegen, ...

Though not directly related to the implementation, special thanks are
going to Yves Bertot, Pierre Castéran, Adam Chlipala, and Benjamin
Pierce for the excellent teaching materials they provided.

| Paris, April 2010
| Hugo Herbelin
|

Credits: version 8.4
--------------------

Coq version 8.4 contains the result of three long-term projects: a new
modular library of arithmetic by Pierre Letouzey, a new proof engine by
Arnaud Spiwack and a new communication protocol for |CoqIDE| by Vincent
Gross.

The new modular library of arithmetic extends, generalizes and unifies
the existing libraries on Peano arithmetic (types nat, N and BigN),
positive arithmetic (type positive), integer arithmetic (Z and BigZ) and
machine word arithmetic (type Int31). It provides with unified notations
(e.g. systematic use of add and mul for denoting the addition and
multiplication operators), systematic and generic development of
operators and properties of these operators for all the types mentioned
above, including gcd, pcm, power, square root, base 2 logarithm,
division, modulo, bitwise operations, logical shifts, comparisons,
iterators, ...

The most visible feature of the new proof engine is the support for
structured scripts (bullets and proof brackets) but, even if yet not
user-available, the new engine also provides the basis for refining
existential variables using tactics, for applying tactics to several
goals simultaneously, for reordering goals, all features which are
planned for the next release. The new proof engine forced Pierre Letouzey
to reimplement info and Show Script differently.

Before version 8.4, |CoqIDE| was linked to |Coq| with the graphical
interface living in a separate thread. From version 8.4, |CoqIDE| is a
separate process communicating with |Coq| through a textual channel. This
allows for a more robust interfacing, the ability to interrupt |Coq|
without interrupting the interface, and the ability to manage several
sessions in parallel. Relying on the infrastructure work made by Vincent
Gross, Pierre Letouzey, Pierre Boutillier and Pierre-Marie Pédrot
contributed many various refinements of |CoqIDE|.

Coq 8.4 also comes with a bunch of various smaller-scale changes
and improvements regarding the different components of the system.

The underlying logic has been extended with :math:`\eta`-conversion
thanks to Hugo Herbelin, Stéphane Glondu and Benjamin Grégoire. The
addition of :math:`\eta`-conversion is justified by the confidence that
the formulation of the Calculus of Inductive Constructions based on
typed equality (such as the one considered in Lee and Werner to build a
set-theoretic model of CIC :cite:`LeeWerner11`) is
applicable to the concrete implementation of |Coq|.

The underlying logic benefited also from a refinement of the guard
condition for fixpoints by Pierre Boutillier, the point being that it is
safe to propagate the information about structurally smaller arguments
through :math:`\beta`-redexes that are blocked by the “match”
construction (blocked commutative cuts).

Relying on the added permissiveness of the guard condition, Hugo
Herbelin could extend the pattern matching compilation algorithm so that
matching over a sequence of terms involving dependencies of a term or of
the indices of the type of a term in the type of other terms is
systematically supported.

Regarding the high-level specification language, Pierre Boutillier
introduced the ability to give implicit arguments to anonymous
functions, Hugo Herbelin introduced the ability to define notations with
several binders (e.g. ``exists x y z, P``), Matthieu Sozeau made the
typeclass inference mechanism more robust and predictable, Enrico
Tassi introduced a command Arguments that generalizes Implicit Arguments
and Arguments Scope for assigning various properties to arguments of
constants. Various improvements in the type inference algorithm were
provided by Matthieu Sozeau and Hugo Herbelin with contributions from
Enrico Tassi.

Regarding tactics, Hugo Herbelin introduced support for referring to
expressions occurring in the goal by pattern in tactics such as set or
destruct. Hugo Herbelin also relied on ideas from Chung-Kil Hur’s Heq
plugin to introduce automatic computation of occurrences to generalize
when using destruct and induction on types with indices. Stéphane Glondu
introduced new tactics :tacn:`constr_eq`, :tacn:`is_evar`, and :tacn:`has_evar`, to be used
when writing complex tactics. Enrico Tassi added support to fine-tuning
the behavior of :tacn:`simpl`. Enrico Tassi added the ability to specify over
which variables of a section a lemma has to be exactly generalized.
Pierre Letouzey added a tactic timeout and the interruptibility of
:tacn:`vm_compute`. Bug fixes and miscellaneous improvements of the tactic
language came from Hugo Herbelin, Pierre Letouzey and Matthieu Sozeau.

Regarding decision tactics, Loïc Pottier maintained nsatz, moving in
particular to a typeclass based reification of goals while Frédéric
Besson maintained Micromega, adding in particular support for division.

Regarding vernacular commands, Stéphane Glondu provided new commands to
analyze the structure of type universes.

Regarding libraries, a new library about lists of a given length (called
vectors) has been provided by Pierre Boutillier. A new instance of
finite sets based on Red-Black trees and provided by Andrew Appel has
been adapted for the standard library by Pierre Letouzey. In the library
of real analysis, Yves Bertot changed the definition of :math:`\pi` and
provided a proof of the long-standing fact yet remaining unproved in
this library, namely that :math:`sin \frac{\pi}{2} =
1`.

Pierre Corbineau maintained the Mathematical Proof Language (C-zar).

Bruno Barras and Benjamin Grégoire maintained the call-by-value
reduction machines.

The extraction mechanism benefited from several improvements provided by
Pierre Letouzey.

Pierre Letouzey maintained the module system, with contributions from
Élie Soubiran.

Julien Forest maintained the Function command.

Matthieu Sozeau maintained the setoid rewriting mechanism.

Coq related tools have been upgraded too. In particular, coq\_makefile
has been largely revised by Pierre Boutillier. Also, patches from Adam
Chlipala for coqdoc have been integrated by Pierre Boutillier.

Bruno Barras and Pierre Letouzey maintained the `coqchk` checker.

Pierre Courtieu and Arnaud Spiwack contributed new features for using
Coq through Proof General.

The Dp plugin has been removed. Use the plugin provided with Why 3
instead (http://why3.lri.fr/).

Under the hood, the |Coq| architecture benefited from improvements in
terms of efficiency and robustness, especially regarding universes
management and existential variables management, thanks to Pierre
Letouzey and Yann Régis-Gianas with contributions from Stéphane Glondu
and Matthias Puech. The build system is maintained by Pierre Letouzey
with contributions from Stéphane Glondu and Pierre Boutillier.

A new backtracking mechanism simplifying the task of external interfaces
has been designed by Pierre Letouzey.

The general maintenance was done by Pierre Letouzey, Hugo Herbelin,
Pierre Boutillier, Matthieu Sozeau and Stéphane Glondu with also
specific contributions from Guillaume Melquiond, Julien Narboux and
Pierre-Marie Pédrot.

Packaging tools were provided by Pierre Letouzey (Windows), Pierre
Boutillier (MacOS), Stéphane Glondu (Debian). Releasing, testing and
benchmarking support was provided by Jean-Marc Notin.

Many suggestions for improvements were motivated by feedback from users,
on either the bug tracker or the Coq-Club mailing list. Special thanks
are going to the users who contributed patches, starting with Tom
Prince. Other patch contributors include Cédric Auger, David Baelde, Dan
Grayson, Paolo Herms, Robbert Krebbers, Marc Lasson, Hendrik Tews and
Eelis van der Weegen.

| Paris, December 2011
| Hugo Herbelin
|

Credits: version 8.5
--------------------

Coq version 8.5 contains the result of five specific long-term projects:

-  A new asynchronous evaluation and compilation mode by Enrico Tassi
   with help from Bruno Barras and Carst Tankink.

-  Full integration of the new proof engine by Arnaud Spiwack helped by
   Pierre-Marie Pédrot,

-  Addition of conversion and reduction based on native compilation by
   Maxime Dénès and Benjamin Grégoire.

-  Full universe polymorphism for definitions and inductive types by
   Matthieu Sozeau.

-  An implementation of primitive projections with
   :math:`\eta`-conversion bringing significant performance improvements
   when using records by Matthieu Sozeau.

The full integration of the proof engine, by Arnaud Spiwack and
Pierre-Marie Pédrot, brings to primitive tactics and the user level Ltac
language dependent subgoals, deep backtracking and multiple goal
handling, along with miscellaneous features and an improved potential
for future modifications. Dependent subgoals allow statements in a goal
to mention the proof of another. Proofs of unsolved subgoals appear as
existential variables. Primitive backtracking makes it possible to write
a tactic with several possible outcomes which are tried successively
when subsequent tactics fail. Primitives are also available to control
the backtracking behavior of tactics. Multiple goal handling paves the
way for smarter automation tactics. It is currently used for simple goal
manipulation such as goal reordering.

The way |Coq| processes a document in batch and interactive mode has been
redesigned by Enrico Tassi with help from Bruno Barras. Opaque proofs,
the text between Proof and Qed, can be processed asynchronously,
decoupling the checking of definitions and statements from the checking
of proofs. It improves the responsiveness of interactive development,
since proofs can be processed in the background. Similarly, compilation
of a file can be split into two phases: the first one checking only
definitions and statements and the second one checking proofs. A file
resulting from the first phase – with the .vio extension – can be
already Required. All .vio files can be turned into complete .vo files
in parallel. The same infrastructure also allows terminating tactics to
be run in parallel on a set of goals via the ``par:`` goal selector.

|CoqIDE| was modified to cope with asynchronous checking of the document.
Its source code was also made separate from that of |Coq|, so that |CoqIDE|
no longer has a special status among user interfaces, paving the way for
decoupling its release cycle from that of |Coq| in the future.

Carst Tankink developed a |Coq| back-end for user interfaces built on
Makarius Wenzel’s Prover IDE framework (PIDE), like PIDE/jEdit (with
help from Makarius Wenzel) or PIDE/Coqoon (with help from Alexander
Faithfull and Jesper Bengtson). The development of such features was
funded by the Paral-ITP French ANR project.

The full universe polymorphism extension was designed by Matthieu
Sozeau. It conservatively extends the universes system and core calculus
with definitions and inductive declarations parameterized by universes
and constraints. It is based on a modification of the kernel
architecture to handle constraint checking only, leaving the generation
of constraints to the refinement/type inference engine. Accordingly,
tactics are now fully universe aware, resulting in more localized error
messages in case of inconsistencies and allowing higher-level algorithms
like unification to be entirely type safe. The internal representation
of universes has been modified but this is invisible to the user.

The underlying logic has been extended with :math:`\eta`-conversion for
records defined with primitive projections by Matthieu Sozeau. This
additional form of :math:`\eta`-conversion is justified using the same
principle than the previously added :math:`\eta`-conversion for function
types, based on formulations of the Calculus of Inductive Constructions
with typed equality. Primitive projections, which do not carry the
parameters of the record and are rigid names (not defined as a
pattern matching construct), make working with nested records more
manageable in terms of time and space consumption. This extension and
universe polymorphism were carried out partly while Matthieu Sozeau was
working at the IAS in Princeton.

The guard condition has been made compliant with extensional equality
principles such as propositional extensionality and univalence, thanks
to Maxime Dénès and Bruno Barras. To ensure compatibility with the
univalence axiom, a new flag ``-indices-matter`` has been implemented,
taking into account the universe levels of indices when computing the
levels of inductive types. This supports using |Coq| as a tool to explore
the relations between homotopy theory and type theory.

Maxime Dénès and Benjamin Grégoire developed an implementation of
conversion test and normal form computation using the OCaml native
compiler. It complements the virtual machine conversion offering much
faster computation for expensive functions.

Coq 8.5 also comes with a bunch of many various smaller-scale changes
and improvements regarding the different components of the system. We
shall only list a few of them.

Pierre Boutillier developed an improved tactic for simplification of
expressions called :tacn:`cbn`.

Maxime Dénès maintained the bytecode-based reduction machine. Pierre
Letouzey maintained the extraction mechanism.

Pierre-Marie Pédrot has extended the syntax of terms to, experimentally,
allow holes in terms to be solved by a locally specified tactic.

Existential variables are referred to by identifiers rather than mere
numbers, thanks to Hugo Herbelin who also improved the tactic language
here and there.

Error messages for universe inconsistencies have been improved by
Matthieu Sozeau. Error messages for unification and type inference
failures have been improved by Hugo Herbelin, Pierre-Marie Pédrot and
Arnaud Spiwack.

Pierre Courtieu contributed new features for using |Coq| through Proof
General and for better interactive experience (bullets, Search, etc).

The efficiency of the whole system has been significantly improved
thanks to contributions from Pierre-Marie Pédrot.

A distribution channel for |Coq| packages using the OPAM tool has been
initiated by Thomas Braibant and developed by Guillaume Claret, with
contributions by Enrico Tassi and feedback from Hugo Herbelin.

Packaging tools were provided by Pierre Letouzey and Enrico Tassi
(Windows), Pierre Boutillier, Matthieu Sozeau and Maxime Dénès (MacOS
X). Maxime Dénès improved significantly the testing and benchmarking
support.

Many power users helped to improve the design of the new features via
the bug tracker, the coq development mailing list or the Coq-Club
mailing list. Special thanks are going to the users who contributed
patches and intensive brain-storming, starting with Jason Gross,
Jonathan Leivent, Greg Malecha, Clément Pit-Claudel, Marc Lasson, Lionel
Rieg. It would however be impossible to mention with precision all names
of people who to some extent influenced the development.

Version 8.5 is one of the most important releases of |Coq|. Its development
spanned over about 3 years and a half with about one year of
beta-testing. General maintenance during part or whole of this period
has been done by Pierre Boutillier, Pierre Courtieu, Maxime Dénès, Hugo
Herbelin, Pierre Letouzey, Guillaume Melquiond, Pierre-Marie Pédrot,
Matthieu Sozeau, Arnaud Spiwack, Enrico Tassi as well as Bruno Barras,
Yves Bertot, Frédéric Besson, Xavier Clerc, Pierre Corbineau,
Jean-Christophe Filliâtre, Julien Forest, Sébastien Hinderer, Assia
Mahboubi, Jean-Marc Notin, Yann Régis-Gianas, François Ripault, Carst
Tankink. Maxime Dénès coordinated the release process.

| Paris, January 2015, revised December 2015,
| Hugo Herbelin, Matthieu Sozeau and the |Coq| development team
|

Credits: version 8.6
--------------------

Coq version 8.6 contains the result of refinements, stabilization of
8.5’s features and cleanups of the internals of the system. Over the
year of (now time-based) development, about 450 bugs were resolved and
over 100 contributions integrated. The main user visible changes are:

-  A new, faster state-of-the-art universe constraint checker, by
   Jacques-Henri Jourdan.

-  In |CoqIDE| and other asynchronous interfaces, more fine-grained
   asynchronous processing and error reporting by Enrico Tassi, making
   |Coq| capable of recovering from errors and continue processing the
   document.

-  More access to the proof engine features from Ltac: goal management
   primitives, range selectors and a :tacn:`typeclasses eauto` engine handling
   multiple goals and multiple successes, by Cyprien Mangin, Matthieu
   Sozeau and Arnaud Spiwack.

-  Tactic behavior uniformization and specification, generalization of
   intro-patterns by Hugo Herbelin and others.

-  A brand new warning system allowing to control warnings, turn them
   into errors or ignore them selectively by Maxime Dénès, Guillaume
   Melquiond, Pierre-Marie Pédrot and others.

-  Irrefutable patterns in abstractions, by Daniel de Rauglaudre.

-  The ssreflect subterm selection algorithm by Georges Gonthier and
   Enrico Tassi is now accessible to tactic writers through the
   ssrmatching plugin.

-  Integration of LtacProf, a profiler for Ltac by Jason Gross, Paul
   Steckler, Enrico Tassi and Tobias Tebbi.

Coq 8.6 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system. We shall
only list a few of them.

The iota reduction flag is now a shorthand for match, fix and cofix
flags controlling the corresponding reduction rules (by Hugo Herbelin
and Maxime Dénès).

Maxime Dénès maintained the native compilation machinery.

Pierre-Marie Pédrot separated the Ltac code from general purpose
tactics, and generalized and rationalized the handling of generic
arguments, allowing to create new versions of Ltac more easily in the
future.

In patterns and terms, @, abbreviations and notations are now
interpreted the same way, by Hugo Herbelin.

Name handling for universes has been improved by Pierre-Marie Pédrot and
Matthieu Sozeau. The minimization algorithm has been improved by
Matthieu Sozeau.

The unifier has been improved by Hugo Herbelin and Matthieu Sozeau,
fixing some incompatibilities introduced in |Coq| 8.5. Unification
constraints can now be left floating around and be seen by the user
thanks to a new option. The Keyed Unification mode has been improved by
Matthieu Sozeau.

The typeclass resolution engine and associated proof-search tactic have
been reimplemented on top of the proof-engine monad, providing better
integration in tactics, and new options have been introduced to control
it, by Matthieu Sozeau with help from Théo Zimmermann.

The efficiency of the whole system has been significantly improved
thanks to contributions from Pierre-Marie Pédrot, Maxime Dénès and
Matthieu Sozeau and performance issue tracking by Jason Gross and Paul
Steckler.

Standard library improvements by Jason Gross, Sébastien Hinderer, Pierre
Letouzey and others.

Emilio Jesús Gallego Arias contributed many cleanups and refactorings of
the pretty-printing and user interface communication components.

Frédéric Besson maintained the micromega tactic.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Claret, Guillaume Melquiond, Matthieu Sozeau, Enrico Tassi and others. A
list of packages is now available at https://coq.inria.fr/opam/www/.

Packaging tools and software development kits were prepared by Michael
Soegtrop with the help of Maxime Dénès and Enrico Tassi for Windows, and
Maxime Dénès and Matthieu Sozeau for MacOS X. Packages are now regularly
built on the continuous integration server. |Coq| now comes with a META
file usable with ocamlfind, contributed by Emilio Jesús Gallego Arias,
Gregory Malecha, and Matthieu Sozeau.

Matej Košík maintained and greatly improved the continuous integration
setup and the testing of |Coq| contributions. He also contributed many API
improvements and code cleanups throughout the system.

The contributors for this version are Bruno Barras, C.J. Bell, Yves
Bertot, Frédéric Besson, Pierre Boutillier, Tej Chajed, Guillaume
Claret, Xavier Clerc, Pierre Corbineau, Pierre Courtieu, Maxime Dénès,
Ricky Elrod, Emilio Jesús Gallego Arias, Jason Gross, Hugo Herbelin,
Sébastien Hinderer, Jacques-Henri Jourdan, Matej Košík, Xavier Leroy,
Pierre Letouzey, Gregory Malecha, Cyprien Mangin, Erik Martin-Dorel,
Guillaume Melquiond, Clément Pit–Claudel, Pierre-Marie Pédrot, Daniel de
Rauglaudre, Lionel Rieg, Gabriel Scherer, Thomas Sibut-Pinote, Matthieu
Sozeau, Arnaud Spiwack, Paul Steckler, Enrico Tassi, Laurent Théry,
Nickolai Zeldovich and Théo Zimmermann. The development process was
coordinated by Hugo Herbelin and Matthieu Sozeau with the help of Maxime
Dénès, who was also in charge of the release process.

Many power users helped to improve the design of the new features via
the bug tracker, the pull request system, the |Coq| development mailing
list or the Coq-Club mailing list. Special thanks to the users who
contributed patches and intensive brain-storming and code reviews,
starting with Cyril Cohen, Jason Gross, Robbert Krebbers, Jonathan
Leivent, Xavier Leroy, Gregory Malecha, Clément Pit–Claudel, Gabriel
Scherer and Beta Ziliani. It would however be impossible to mention
exhaustively the names of everybody who to some extent influenced the
development.

Version 8.6 is the first release of |Coq| developed on a time-based
development cycle. Its development spanned 10 months from the release of
Coq 8.5 and was based on a public roadmap. To date, it contains more
external contributions than any previous |Coq| system. Code reviews were
systematically done before integration of new features, with an
important focus given to compatibility and performance issues, resulting
in a hopefully more robust release than |Coq| 8.5.

Coq Enhancement Proposals (CEPs for short) were introduced by Enrico
Tassi to provide more visibility and a discussion period on new
features, they are publicly available https://github.com/coq/ceps.

Started during this period, an effort is led by Yves Bertot and Maxime
Dénès to put together a |Coq| consortium.

| Paris, November 2016,
| Matthieu Sozeau and the |Coq| development team
|

Credits: version 8.7
--------------------

|Coq| version 8.7 contains the result of refinements, stabilization of features
and cleanups of the internals of the system along with a few new features. The
main user visible changes are:

- New tactics: variants of tactics supporting existential variables :tacn:`eassert`,
  :tacn:`eenough`, etc... by Hugo Herbelin. Tactics ``extensionality in H`` and
  :tacn:`inversion_sigma` by Jason Gross, ``specialize with ...`` accepting partial bindings
  by Pierre Courtieu.

- ``Cumulative Polymorphic Inductive`` types, allowing cumulativity of universes to
  go through applied inductive types, by Amin Timany and Matthieu Sozeau.

- Integration of the SSReflect plugin and its documentation in the reference
  manual, by Enrico Tassi, Assia Mahboubi and Maxime Dénès.

- The ``coq_makefile`` tool was completely redesigned to improve its maintainability
  and the extensibility of generated Makefiles, and to make ``_CoqProject`` files
  more palatable to IDEs by Enrico Tassi.

|Coq| 8.7 involved a large amount of work on cleaning and speeding up the code
base, notably the work of Pierre-Marie Pédrot on making the tactic-level system
insensitive to existential variable expansion, providing a safer API to plugin
writers and making the code more robust. The ``dev/doc/changes.txt`` file
documents the numerous changes to the implementation and improvements of
interfaces. An effort to provide an official, streamlined API to plugin writers
is in progress, thanks to the work of Matej Košík.

Version 8.7 also comes with a bunch of smaller-scale changes and improvements
regarding the different components of the system. We shall only list a few of
them.

The efficiency of the whole system has been significantly improved thanks to
contributions from Pierre-Marie Pédrot, Maxime Dénès and Matthieu Sozeau and
performance issue tracking by Jason Gross and Paul Steckler.

Thomas Sibut-Pinote and Hugo Herbelin added support for side effect hooks in
cbv, cbn and simpl. The side effects are provided via a plugin available at
https://github.com/herbelin/reduction-effects/.

The BigN, BigZ, BigQ libraries are no longer part of the |Coq| standard library,
they are now provided by a separate repository https://github.com/coq/bignums,
maintained by Pierre Letouzey.

In the Reals library, ``IZR`` has been changed to produce a compact representation
of integers and real constants are now represented using ``IZR`` (work by
Guillaume Melquiond).

Standard library additions and improvements by Jason Gross, Pierre Letouzey and
others, documented in the ``CHANGES.md`` file.

The mathematical proof language/declarative mode plugin was removed from the
archive.

The OPAM repository for |Coq| packages has been maintained by Guillaume Melquiond,
Matthieu Sozeau, Enrico Tassi with contributions from many users. A list of
packages is available at https://coq.inria.fr/opam/www/.

Packaging tools and software development kits were prepared by Michael Soegtrop
with the help of Maxime Dénès and Enrico Tassi for Windows, and Maxime Dénès for
MacOS X. Packages are regularly built on the Travis continuous integration
server.

The contributors for this version are Abhishek Anand, C.J. Bell, Yves Bertot,
Frédéric Besson, Tej Chajed, Pierre Courtieu, Maxime Dénès, Julien Forest,
Gaëtan Gilbert, Jason Gross, Hugo Herbelin, Emilio Jesús Gallego Arias, Ralf
Jung, Matej Košík, Xavier Leroy, Pierre Letouzey, Assia Mahboubi, Cyprien
Mangin, Erik Martin-Dorel, Olivier Marty, Guillaume Melquiond, Sam Pablo Kuper,
Benjamin Pierce, Pierre-Marie Pédrot, Lars Rasmusson, Lionel Rieg, Valentin
Robert, Yann Régis-Gianas, Thomas Sibut-Pinote, Michael Soegtrop, Matthieu
Sozeau, Arnaud Spiwack, Paul Steckler, George Stelle, Pierre-Yves Strub, Enrico
Tassi, Hendrik Tews, Amin Timany, Laurent Théry, Vadim Zaliva and Théo
Zimmermann.

The development process was coordinated by Matthieu Sozeau with the help of
Maxime Dénès, who was also in charge of the release process. Théo Zimmermann is
the maintainer of this release.

Many power users helped to improve the design of the new features via the bug
tracker, the pull request system, the |Coq| development mailing list or the
Coq-Club mailing list. Special thanks to the users who contributed patches and
intensive brain-storming and code reviews, starting with Jason Gross, Ralf Jung,
Robbert Krebbers, Xavier Leroy, Clément Pit–Claudel and Gabriel Scherer. It
would however be impossible to mention exhaustively the names of everybody who
to some extent influenced the development.

Version 8.7 is the second release of |Coq| developed on a time-based development
cycle. Its development spanned 9 months from the release of |Coq| 8.6 and was
based on a public road-map. It attracted many external contributions. Code
reviews and continuous integration testing were systematically used before
integration of new features, with an important focus given to compatibility and
performance issues, resulting in a hopefully more robust release than |Coq| 8.6
while maintaining compatibility.

|Coq| Enhancement Proposals (CEPs for short) and open pull request discussions
were used to discuss publicly the new features.

The |Coq| consortium, an organization directed towards users and supporters of the
system, is now upcoming and will rely on Inria’s newly created Foundation.

| Paris, August 2017,
| Matthieu Sozeau and the |Coq| development team
|

Credits: version 8.8
--------------------

|Coq| version 8.8 contains the result of refinements and stabilization of
features and deprecations, cleanups of the internals of the system along
with a few new features. The main user visible changes are:

- Kernel: fix a subject reduction failure due to allowing fixpoints
  on non-recursive values, by Matthieu Sozeau.
  Handling of evars in the VM (the kernel still does not accept evars)
  by Pierre-Marie Pédrot.

- Notations: many improvements on recursive notations and support for
  destructuring patterns in the syntax of notations by Hugo Herbelin.

- Proof language: tacticals for profiling, timing and checking success
  or failure of tactics by Jason Gross. The focusing bracket ``{``
  supports single-numbered goal selectors, e.g. ``2:{``, by Théo
  Zimmermann.

- Vernacular: deprecation of commands and more uniform handling of the
  ``Local`` flag, by Vincent Laporte and Maxime Dénès, part of a larger
  attribute system overhaul. Experimental ``Show Extraction`` command by
  Pierre Letouzey. Coercion now accepts ``Prop`` or ``Type`` as a source
  by Arthur Charguéraud. ``Export`` modifier for options allowing to
  export the option to modules that ``Import`` and not only ``Require``
  a module, by Pierre-Marie Pédrot.

- Universes: many user-level and API level enhancements: qualified
  naming and printing, variance annotations for cumulative inductive
  types, more general constraints and enhancements of the minimization
  heuristics, interaction with modules by Gaëtan Gilbert, Pierre-Marie
  Pédrot and Matthieu Sozeau.

- Library: Decimal Numbers library by Pierre Letouzey and various small
  improvements.

- Documentation: a large community effort resulted in the migration
  of the reference manual to the Sphinx documentation tool. The result
  is this manual. The new documentation infrastructure (based on Sphinx)
  is by Clément Pit-Claudel. The migration was coordinated by Maxime Dénès
  and Paul Steckler, with some help of Théo Zimmermann during the
  final integration phase. The 14 people who ported the manual are
  Calvin Beck, Heiko Becker, Yves Bertot, Maxime Dénès, Richard Ford,
  Pierre Letouzey, Assia Mahboubi, Clément Pit-Claudel,
  Laurence Rideau, Matthieu Sozeau, Paul Steckler, Enrico Tassi,
  Laurent Théry, Nikita Zyuzin.

- Tools: experimental ``-mangle-names`` option to ``coqtop``/``coqc`` for
  linting proof scripts, by Jasper Hugunin.

On the implementation side, the ``dev/doc/changes.md`` file
documents the numerous changes to the implementation and improvements of
interfaces. The file provides guidelines on porting a plugin to the new
version.

Version 8.8 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system.
Most important ones are documented in the ``CHANGES.md`` file.

The efficiency of the whole system has seen improvements thanks to
contributions from Gaëtan Gilbert, Pierre-Marie Pédrot, Maxime Dénès and
Matthieu Sozeau and performance issue tracking by Jason Gross and Paul
Steckler.

The official wiki and the bugtracker of |Coq| migrated to the GitHub
platform, thanks to the work of Pierre Letouzey and Théo
Zimmermann. Gaëtan Gilbert, Emilio Jesús Gallego Arias worked on
maintaining and improving the continuous integration system.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Melquiond, Matthieu Sozeau, Enrico Tassi with contributions from many
users. A list of packages is available at https://coq.inria.fr/opam/www/.

The 44 contributors for this version are Yves Bertot, Joachim Breitner, Tej
Chajed, Arthur Charguéraud, Jacques-Pascal Deplaix, Maxime Dénès, Jim Fehrle,
Julien Forest, Yannick Forster, Gaëtan Gilbert, Jason Gross, Samuel Gruetter,
Thomas Hebb, Hugo Herbelin, Jasper Hugunin, Emilio Jesus Gallego Arias, Ralf
Jung, Johannes Kloos, Matej Košík, Robbert Krebbers, Tony Beta Lambda, Vincent
Laporte, Peter LeFanu Lumsdaine, Pierre Letouzey, Farzon Lotfi, Cyprien Mangin,
Guillaume Melquiond, Raphaël Monat, Carl Patenaude Poulin, Pierre-Marie Pédrot,
Clément Pit-Claudel, Matthew Ryan, Matt Quinn, Sigurd Schneider, Bernhard
Schommer, Michael Soegtrop, Matthieu Sozeau, Arnaud Spiwack, Paul Steckler,
Enrico Tassi, Anton Trunov, Martin Vassor, Vadim Zaliva and Théo Zimmermann.

Version 8.8 is the third release of |Coq| developed on a time-based
development cycle. Its development spanned 6 months from the release of
|Coq| 8.7 and was based on a public roadmap. The development process
was coordinated by Matthieu Sozeau. Maxime Dénès was in charge of the
release process. Théo Zimmermann is the maintainer of this release.

Many power users helped to improve the design of the new features via
the bug tracker, the pull request system, the |Coq| development mailing
list or the coq-club@inria.fr mailing list. Special thanks to the users who
contributed patches and intensive brain-storming and code reviews,
starting with Jason Gross, Ralf Jung, Robbert Krebbers and Amin Timany.
It would however be impossible to mention exhaustively the names
of everybody who to some extent influenced the development.

The |Coq| consortium, an organization directed towards users and
supporters of the system, is now running and employs Maxime Dénès.
The contacts of the Coq Consortium are Yves Bertot and Maxime Dénès.

| Santiago de Chile, March 2018,
| Matthieu Sozeau for the |Coq| development team
|

Credits: version 8.9
--------------------

|Coq| version 8.9 contains the result of refinements and stabilization
of features and deprecations or removals of deprecated features,
cleanups of the internals of the system and API along with a few new
features. This release includes many user-visible changes, including
deprecations that are documented in ``CHANGES.md`` and new features that
are documented in the reference manual. Here are the most important
changes:

- Kernel: mutually recursive records are now supported, by Pierre-Marie
  Pédrot.

- Notations:

  - Support for autonomous grammars of terms called “custom entries”, by
    Hugo Herbelin (see Section :ref:`custom-entries` of the reference
    manual).

  - Deprecated notations of the standard library will be removed in the
    next version of |Coq|, see the ``CHANGES.md`` file for a script to
    ease porting, by Jason Gross and Jean-Christophe Léchenet.

  - Added the :cmd:`Numeral Notation` command for registering decimal
    numeral notations for custom types, by Daniel de Rauglaudre, Pierre
    Letouzey and Jason Gross.

- Tactics: Introduction tactics :tacn:`intro`/:tacn:`intros` on a goal that is an
  existential variable now force a refinement of the goal into a
  dependent product rather than failing, by Hugo Herbelin.

- Decision procedures: deprecation of tactic ``romega`` in favor of
  :tacn:`lia` and removal of ``fourier``, replaced by :tacn:`lra` which
  subsumes it, by Frédéric Besson, Maxime Dénès, Vincent Laporte and
  Laurent Théry.

- Proof language: focusing bracket ``{`` now supports named
  :ref:`goals <curly-braces>`, e.g. ``[x]:{`` will focus
  on a goal (existential variable) named ``x``, by Théo Zimmermann.

- SSReflect: the implementation of delayed clear was simplified by
  Enrico Tassi: the variables are always renamed using inaccessible
  names when the clear switch is processed and finally cleared at the
  end of the intro pattern. In addition to that, the use-and-discard flag
  ``{}`` typical of rewrite rules can now be also applied to views,
  e.g. ``=> {}/v`` applies ``v`` and then clears ``v``. See Section
  :ref:`introduction_ssr`.

- Vernacular:

  - Experimental support for :ref:`attributes <gallina-attributes>` on
    commands, by Vincent Laporte, as in ``#[local] Lemma foo : bar.``
    Tactics and tactic notations now support the ``deprecated``
    attribute.

  - Removed deprecated commands ``Arguments Scope`` and ``Implicit
    Arguments`` in favor of :cmd:`Arguments`, with the help of Jasper
    Hugunin.

  - New flag :flag:`Uniform Inductive Parameters` by Jasper Hugunin to
    avoid repeating uniform parameters in constructor declarations.

  - New commands :cmd:`Hint Variables` and :cmd:`Hint Constants`, by
    Matthieu Sozeau, for controlling the opacity status of variables and
    constants in hint databases. It is recommended to always use these
    commands after creating a hint databse with :cmd:`Create HintDb`.

  - Multiple sections with the same name are now allowed, by Jasper
    Hugunin.

- Library: additions and changes in the ``VectorDef``, ``Ascii``, and
  ``String`` libraries. Syntax notations are now available only when using
  ``Import`` of libraries and not merely ``Require``, by various
  contributors (source of incompatibility, see ``CHANGES.md`` for details).

- Toplevels: ``coqtop`` and ``coqide`` can now display diffs between proof
  steps in color, using the :opt:`Diffs` option, by Jim Fehrle.

- Documentation: we integrated a large number of fixes to the new Sphinx
  documentation by various contributors, coordinated by Clément
  Pit-Claudel and Théo Zimmermann.

- Tools: removed the ``gallina`` utility and the homebrewed ``Emacs`` mode.

- Packaging: as in |Coq| 8.8.2, the Windows installer now includes many
  more external packages that can be individually selected for
  installation, by Michael Soegtrop.

Version 8.9 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system.  Most
important ones are documented in the ``CHANGES.md`` file.

On the implementation side, the ``dev/doc/changes.md`` file documents
the numerous changes to the implementation and improvements of
interfaces. The file provides guidelines on porting a plugin to the new
version and a plugin development tutorial kept in sync with Coq was
introduced by Yves Bertot http://github.com/ybertot/plugin_tutorials.
The new ``dev/doc/critical-bugs`` file documents the known critical bugs
of |Coq| and affected releases.

The efficiency of the whole system has seen improvements thanks to
contributions from Gaëtan Gilbert, Pierre-Marie Pédrot, and Maxime Dénès.

Maxime Dénès, Emilio Jesús Gallego Arias, Gaëtan Gilbert, Michael
Soegtrop, Théo Zimmermann worked on maintaining and improving the
continuous integration system.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Melquiond, Matthieu Sozeau, Enrico Tassi with contributions from many
users. A list of packages is available at https://coq.inria.fr/opam/www/.

The 54 contributors for this version are Léo Andrès, Rin Arakaki,
Benjamin Barenblat, Langston Barrett, Siddharth Bhat, Martin Bodin,
Simon Boulier, Timothy Bourke, Joachim Breitner, Tej Chajed, Arthur
Charguéraud, Pierre Courtieu, Maxime Dénès, Andres Erbsen, Jim Fehrle,
Julien Forest, Emilio Jesus Gallego Arias, Gaëtan Gilbert, Matěj
Grabovský, Jason Gross, Samuel Gruetter, Armaël Guéneau, Hugo Herbelin,
Jasper Hugunin, Ralf Jung, Sam Pablo Kuper, Ambroise Lafont, Leonidas
Lampropoulos, Vincent Laporte, Peter LeFanu Lumsdaine, Pierre Letouzey,
Jean-Christophe Léchenet, Nick Lewycky, Yishuai Li, Sven M. Hallberg,
Assia Mahboubi, Cyprien Mangin, Guillaume Melquiond, Perry E. Metzger,
Clément Pit-Claudel, Pierre-Marie Pédrot, Daniel R. Grayson, Kazuhiko
Sakaguchi, Michael Soegtrop, Matthieu Sozeau, Paul Steckler, Enrico
Tassi, Laurent Théry, Anton Trunov, whitequark, Théo Winterhalter,
Zeimer, Beta Ziliani, Théo Zimmermann.

Many power users helped to improve the design of the new features via
the issue and pull request system, the |Coq| development mailing list or
the coq-club@inria.fr mailing list. It would be impossible to mention
exhaustively the names of everybody who to some extent influenced the
development.

Version 8.9 is the fourth release of |Coq| developed on a time-based
development cycle. Its development spanned 7 months from the release of
|Coq| 8.8. The development moved to a decentralized merging process
during this cycle. Guillaume Melquiond was in charge of the release
process and is the maintainer of this release. This release is the
result of ~2,000 commits and ~500 PRs merged, closing 75+ issues.

The |Coq| development team welcomed Vincent Laporte, a new |Coq|
engineer working with Maxime Dénès in the |Coq| consortium.

| Paris, November 2018,
| Matthieu Sozeau for the |Coq| development team
|
