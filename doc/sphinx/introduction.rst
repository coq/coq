------------------------
Introduction
------------------------

This document is the Reference Manual of version of the |Coq|  proof
assistant. A companion volume, the |Coq| Tutorial, is provided for the
beginners. It is advised to read the Tutorial first. A
book :cite:`CoqArt` on practical uses of the |Coq| system was
published in 2004 and is a good support for both the beginner and the
advanced user.

The |Coq| system is designed to develop mathematical proofs, and
especially to write formal specifications, programs and to verify that
programs are correct with respect to their specification. It provides a
specification language named |Gallina|. Terms of |Gallina| can represent
programs as well as properties of these programs and proofs of these
properties. Using the so-called *Curry-Howard isomorphism*, programs,
properties and proofs are formalized in the same language called
*Calculus of Inductive Constructions*, that is a
:math:`\lambda`-calculus with a rich type system. All logical judgments
in |Coq| are typing judgments. The very heart of the |Coq| system is the
type-checking algorithm that checks the correctness of proofs, in other
words that checks that a program complies to its specification. |Coq| also
provides an interactive proof assistant to build proofs using specific
programs called *tactics*.

All services of the |Coq| proof assistant are accessible by interpretation
of a command language called *the vernacular*.

Coq has an interactive mode in which commands are interpreted as the
user types them in from the keyboard and a compiled mode where commands
are processed from a file.

-  The interactive mode may be used as a debugging mode in which the
   user can develop his theories and proofs step by step, backtracking
   if needed and so on. The interactive mode is run with the `coqtop` 
   command from the operating system (which we shall assume to be some
   variety of UNIX in the rest of this document).

-  The compiled mode acts as a proof checker taking a file containing a
   whole development in order to ensure its correctness. Moreover,
   |Coq|’s compiler provides an output file containing a compact
   representation of its input. The compiled mode is run with the `coqc`
   command from the operating system.

These two modes are documented in Chapter :ref:`thecoqcommands`.

Other modes of interaction with |Coq| are possible: through an emacs shell
window, an emacs generic user-interface for proof assistant (Proof
General :cite:`ProofGeneral`) or through a customized
interface (PCoq :cite:`Pcoq`). These facilities are not
documented here. There is also a |Coq| Integrated Development Environment
described in :ref:`coqintegrateddevelopmentenvironment`.

How to read this book
=====================

This is a Reference Manual, not a User Manual, so it is not made for a
continuous reading. However, it has some structure that is explained
below.

-  The first part describes the specification language, |Gallina|.
   Chapters :ref:`thegallinaspecificationlanguage` and :ref:`extensionsofgallina` describe the concrete
   syntax as well as the meaning of programs, theorems and proofs in the
   Calculus of Inductive Constructions. Chapter :ref:`thecoqlibrary` describes the
   standard library of |Coq|. Chapter :ref:`calculusofinductiveconstructions` is a mathematical description
   of the formalism. Chapter :ref:`themodulesystem` describes the module
   system.

-  The second part describes the proof engine. It is divided in five
   chapters. Chapter :ref:`vernacularcommands` presents all commands (we
   call them *vernacular commands*) that are not directly related to
   interactive proving: requests to the environment, complete or partial
   evaluation, loading and compiling files. How to start and stop
   proofs, do multiple proofs in parallel is explained in
   Chapter :ref:`proofhandling`. In Chapter :ref:`tactics`, all commands that
   realize one or more steps of the proof are presented: we call them
   *tactics*. The language to combine these tactics into complex proof
   strategies is given in Chapter :ref:`thetacticlanguage`. Examples of tactics
   are described in Chapter :ref:`detailedexamplesoftactics`.

-  The third part describes how to extend the syntax of |Coq|. It
   corresponds to the Chapter :ref:`syntaxextensionsandinterpretationscopes`.

-  In the fourth part more practical tools are documented. First in
   Chapter :ref:`thecoqcommands`, the usage of `coqc` (batch mode) and
   `coqtop` (interactive mode) with their options is described. Then,
   in Chapter :ref:`utilities`, various utilities that come with the
   |Coq| distribution are presented. Finally, Chapter :ref:`coqintegrateddevelopmentenvironment` 
   describes the |Coq| integrated development environment.

-  The fifth part documents a number of advanced features, including coercions,
   canonical structures, typeclasses, program extraction, and specialized
   solvers and tactics. See the table of contents for a complete list.

At the end of the document, after the global index, the user can find
specific indexes for tactics, vernacular commands, and error messages.

List of additional documentation
================================

This manual does not contain all the documentation the user may need
about |Coq|. Various informations can be found in the following documents:

Tutorial
    A companion volume to this reference manual, the |Coq| Tutorial, is
    aimed at gently introducing new users to developing proofs in |Coq|
    without assuming prior knowledge of type theory. In a second step,
    the user can read also the tutorial on recursive types (document
    `RecTutorial.ps`).

Installation
    A text file `INSTALL` that comes with the sources explains how to
    install |Coq|.

The |Coq| standard library
    A commented version of sources of the |Coq| standard library
    (including only the specifications, the proofs are removed) is given
    in the additional document `Library.ps`.
