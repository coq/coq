.. _extensions:

===================
Language extensions
===================

Elaboration extends the language accepted by the Rocq kernel to make it
easier to use.  For example, this lets the user omit most type
annotations because they can be inferred, call functions with implicit
arguments which will be inferred as well, extend the syntax with
notations, factorize branches when pattern-matching, etc.  In this
chapter, we present these language extensions and we give some
explanations on how this language is translated down to the core
language presented in the :ref:`previous chapter <core-language>`.

.. toctree::
   :maxdepth: 1

   evars
   implicit-arguments
   match
   ../../user-extensions/syntax-extensions
   arguments-command
   ../../addendum/implicit-coercions
   ../../addendum/type-classes
   canonical
   ../../addendum/program
   ../../proof-engine/vernacular-commands
