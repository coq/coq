.. _core-language:

=============
Core language
=============

At the heart of the Rocq Prover is the Rocq kernel.  While
users have access to a language with many convenient features such as
:ref:`notations <syntax-extensions-and-notation-scopes>`,
:ref:`implicit arguments <ImplicitArguments>`, etc.  (presented in the
:ref:`next chapter <extensions>`), those features are translated into
the core language (the Calculus of Inductive Constructions) that the
kernel understands, which we present here.  Furthermore, while users
can build proofs interactively using tactics (see Chapter
:ref:`writing-proofs`), the role of these tactics is to incrementally
build a "proof term" which the kernel will verify.  More precisely, a
proof term is a :term:`term` of the Calculus of Inductive
Constructions whose :term:`type` corresponds to a theorem statement.
The kernel is a type checker which verifies that terms have their
expected types.

This separation between the kernel on one hand and the
:ref:`elaboration engine <extensions>` and :ref:`tactics
<writing-proofs>` on the other follows what is known as the :gdef:`de
Bruijn criterion` (keeping a small and well delimited trusted code
base within a proof assistant which can be much more complex).  This
separation makes it necessary to trust only a smaller, critical
component (the kernel) instead of the entire system.  In particular,
users may rely on external plugins that provide advanced and complex
tactics without fear of these tactics being buggy, because the kernel
will have to check their output.

.. toctree::
   :maxdepth: 1

   basic
   sorts
   assumptions
   definitions
   conversion
   ../cic
   variants
   records
   inductive
   coinductive
   sections
   modules
   primitive
   ../../addendum/universe-polymorphism
   ../../addendum/sprop
   ../../addendum/rewrite-rules
