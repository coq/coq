.. _core-language:

=============
Core language
=============

At the heart of the Coq proof assistant is the Coq kernel.  While
users have access to a language with many convenient features such as
notations, implicit arguments, etc. (that are presented in the
:ref:`next chapter <extensions>`), such complex terms get translated
down to a core language (the Calculus of Inductive Constructions) that
the kernel understands, and which we present here.  Furthermore, while
users can build proofs interactively using tactics (see Chapter
:ref:`writing-proofs`), the role of these tactics is to incrementally
build a "proof term" which the kernel will verify.  More precisely, a
proof term is a term of the Calculus of Inductive Constructions whose
type corresponds to a theorem statement.  The kernel is a type checker
which verifies that terms have their expected type.

This separation between the kernel on the one hand and the elaboration
engine and tactics on the other hand follows what is known as the "de
Bruijn criterion" (keeping a small and well delimited trusted code
base within a proof assistant which can be much more complex).  This
separation makes it possible to reduce the trust in the whole system
to trusting a smaller, critical component: the kernel.  In particular,
users may rely on external plugins that provide advanced and complex
tactics without fear of these tactics being buggy, because the kernel
will have to check their output.

.. toctree::
   :maxdepth: 1

   ../gallina-specification-language
   ../cic
   records
   ../../addendum/universe-polymorphism
   ../../addendum/sprop
   sections
   ../module-system
