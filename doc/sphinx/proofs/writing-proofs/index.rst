.. _writing-proofs:

==============
Writing proofs
==============

Coq is an interactive theorem prover, or proof assistant, which means
that proofs can be constructed interactively through a dialog between
the user and the assistant.  The building blocks for this dialog are
tactics which the user will use to represent steps in the proof of a
theorem.

Incomplete proofs have one or more open (unproven) sub-goals.  Each
goal has its own context (a set of assumptions that can be used to
prove the goal).  Tactics can transform goals and contexts.
Internally, the incomplete proof is represented as a partial proof
term, with holes for the unproven sub-goals.

When a proof is complete, the user leaves the proof mode and defers
the verification of the resulting proof term to the :ref:`kernel
<core-language>`.

This chapter is divided in several parts, describing the basic ideas
of the proof mode (during which tactics can be used), and several
flavors of tactics, including the SSReflect proof language.

.. toctree::
   :maxdepth: 1

   ../../proof-engine/proof-handling
   ../../proof-engine/tactics
   ../../proof-engine/ssreflect-proof-language
   ../../proof-engine/detailed-tactic-examples
   ../../user-extensions/proof-schemes
