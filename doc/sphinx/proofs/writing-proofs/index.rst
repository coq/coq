.. _writing-proofs:

===================
Basic proof writing
===================

The Rocq Prover is a proof assistant (or interactive theorem prover), which means
that proofs can be constructed interactively through a dialog between
the user and the assistant.  The building blocks for this dialog are
tactics which the user will use to represent steps in the proof of a
theorem.

The first section presents the proof mode (the core mechanism of the
dialog between the user and the proof assistant).  Then, several
sections describe the available tactics.  The last section covers the
SSReflect proof language, which provides a consistent alternative set
of tactics to the standard basic tactics.

Additional tactics are documented in the next chapter
:ref:`automatic-tactics`.

.. toctree::
   :maxdepth: 1

   proof-mode
   ../../proof-engine/tactics
   equality
   reasoning-inductives
   ../../proof-engine/ssreflect-proof-language
