This document is the Reference Manual of the |Coq| proof assistant.
To start using Coq, it is advised to first read a tutorial.
Links to several tutorials can be found at
https://coq.inria.fr/documentation and
https://github.com/coq/coq/wiki#coq-tutorials

The |Coq| system is designed to develop mathematical proofs, and
especially to write formal specifications, programs and to verify that
programs are correct with respect to their specifications. It provides a
specification language named |Gallina|. Terms of |Gallina| can represent
programs as well as properties of these programs and proofs of these
properties. Using the so-called *Curry-Howard isomorphism*, programs,
properties and proofs are formalized in the same language called
*Calculus of Inductive Constructions*, that is a
:math:`\lambda`-calculus with a rich type system. All logical judgments
in |Coq| are typing judgments. The very heart of the |Coq| system is the
type checking algorithm that checks the correctness of proofs, in other
words that checks that a program complies to its specification. |Coq| also
provides an interactive proof assistant to build proofs using specific
programs called *tactics*.

All services of the |Coq| proof assistant are accessible by interpretation
of a command language called *the vernacular*.

Coq has an interactive mode in which commands are interpreted as the
user types them in from the keyboard and a compiled mode where commands
are processed from a file.

-  In interactive mode, users can develop their theories and proofs step by
   step, and query the system for available theorems and definitions. The
   interactive mode is generally run with the help of an IDE, such
   as CoqIDE, documented in :ref:`coqintegrateddevelopmentenvironment`,
   Emacs with Proof-General :cite:`Asp00` [#PG]_,
   or jsCoq to run Coq in your browser (see https://github.com/ejgallego/jscoq).
   The `coqtop` read-eval-print-loop can also be used directly, for debugging
   purposes.

-  The compiled mode acts as a proof checker taking a file containing a
   whole development in order to ensure its correctness. Moreover,
   |Coq|’s compiler provides an output file containing a compact
   representation of its input. The compiled mode is run with the `coqc`
   command.

.. seealso:: :ref:`thecoqcommands`.

How to read this book
---------------------

This is a Reference Manual, so it is not intended for continuous reading.
We recommend using the various indexes to quickly locate the documentation
you are looking for. There is a global index, and a number of specific indexes
for tactics, vernacular commands, and error messages and warnings.
Nonetheless, the manual has some structure that is explained below.

-  The first part describes the specification language, |Gallina|.
   Chapters :ref:`gallinaspecificationlanguage` and :ref:`extensionsofgallina` describe the concrete
   syntax as well as the meaning of programs, theorems and proofs in the
   Calculus of Inductive Constructions. Chapter :ref:`thecoqlibrary` describes the
   standard library of |Coq|. Chapter :ref:`calculusofinductiveconstructions` is a mathematical description
   of the formalism. Chapter :ref:`themodulesystem` describes the module
   system.

-  The second part describes the proof engine. It is divided in six
   chapters. Chapter :ref:`vernacularcommands` presents all commands (we
   call them *vernacular commands*) that are not directly related to
   interactive proving: requests to the environment, complete or partial
   evaluation, loading and compiling files. How to start and stop
   proofs, do multiple proofs in parallel is explained in
   Chapter :ref:`proofhandling`. In Chapter :ref:`tactics`, all commands that
   realize one or more steps of the proof are presented: we call them
   *tactics*. The language to combine these tactics into complex proof
   strategies is given in Chapter :ref:`ltac`. Examples of tactics
   are described in Chapter :ref:`detailedexamplesoftactics`.
   Finally, the |SSR| proof language is presented in
   Chapter :ref:`thessreflectprooflanguage`.

-  The third part describes how to extend the syntax of |Coq| in
   Chapter :ref:`syntaxextensionsandinterpretationscopes` and how to define
   new induction principles in Chapter :ref:`proofschemes`.

-  In the fourth part more practical tools are documented. First in
   Chapter :ref:`thecoqcommands`, the usage of `coqc` (batch mode) and
   `coqtop` (interactive mode) with their options is described. Then,
   in Chapter :ref:`utilities`, various utilities that come with the
   |Coq| distribution are presented. Finally, Chapter :ref:`coqintegrateddevelopmentenvironment` 
   describes CoqIDE.

-  The fifth part documents a number of advanced features, including coercions,
   canonical structures, typeclasses, program extraction, and specialized
   solvers and tactics. See the table of contents for a complete list.

List of additional documentation
--------------------------------

This manual does not contain all the documentation the user may need
about |Coq|. Various informations can be found in the following documents:

Installation
    A text file `INSTALL` that comes with the sources explains how to
    install |Coq|.

The |Coq| standard library
    A commented version of sources of the |Coq| standard library
    (including only the specifications, the proofs are removed) is
    available at https://coq.inria.fr/stdlib/.
