This is the reference manual of Coq.  Coq is an interactive theorem
prover.  It lets you formalize mathematical concepts and then helps
you interactively generate machine-checked proofs of theorems.
Machine checking gives users much more confidence that the proofs are
correct compared to human-generated and -checked proofs.  Coq has been
used in a number of flagship verification projects, including the
`CompCert verified C compiler <http://compcert.inria.fr/>`_, and has
served to verify the proof of the `four color theorem
<https://github.com/math-comp/fourcolor>`_ (among many other
mathematical formalizations).

Users generate proofs by entering a series of tactics that constitute
steps in the proof.  There are many built-in tactics, some of which
are elementary, while others implement complex decision procedures
(such as :tacn:`lia`, a decision procedure for linear integer
arithmetic).  :ref:`Ltac <ltac>` and its planned replacement,
:ref:`Ltac2 <ltac2>`, provide languages to define new tactics by
combining existing tactics with looping and conditional constructs.
These permit automation of large parts of proofs and sometimes entire
proofs.  Furthermore, users can add novel tactics or functionality by
creating Coq plugins using OCaml.

The Coq kernel, a small part of Coq, does the final verification that
the tactic-generated proof is valid.  Usually the tactic-generated
proof is indeed correct, but delegating proof verification to the
kernel means that even if a tactic is buggy, it won't be able to
introduce an incorrect proof into the system.

Finally, Coq also supports extraction of verified programs to
programming languages such as OCaml and Haskell.  This provides a way
of executing Coq code efficiently and can be used to create verified
software libraries.

To learn Coq, beginners are advised to first start with a tutorial /
book.  Several such tutorials / books are listed at
https://coq.inria.fr/documentation.

This manual is organized in three main parts, plus an appendix:

- **The first part presents the specification language of Coq**, that
  allows to define programs and state mathematical theorems.
  :ref:`core-language` presents the language that the kernel of Coq
  understands.  :ref:`extensions` presents the richer language, with
  notations, implicits, etc. that a user can use and which is
  translated down to the language of the kernel by means of an
  "elaboration process".

- **The second part presents proof mode**, the central
  feature of Coq.  :ref:`writing-proofs` introduces this interactive
  mode and the available proof languages.
  :ref:`automatic-tactics` presents some more advanced tactics, while
  :ref:`writing-tactics` is about the languages that allow a user to
  combine tactics together and develop new ones.

- **The third part shows how to use Coq in practice.**
  :ref:`libraries` presents some of the essential reusable blocks from
  the ecosystem and some particularly important extensions such as the
  program extraction mechanism.  :ref:`tools` documents important
  tools that a user needs to build a Coq project.

- In the appendix, :ref:`history-and-changes` presents the history of
  Coq and changes in recent releases.  This is an important reference
  if you upgrade the version of Coq that you use.  The various
  :ref:`indexes <indexes>` are very useful to **quickly browse the
  manual and find what you are looking for.** They are often the main
  entry point to the manual.
