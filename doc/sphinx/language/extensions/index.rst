.. _extensions:

===================
Language extensions
===================

Elaboration extends the language accepted by the Coq kernel to make it
easier to use.  For example, this lets the user omit most type
annotations because they can be inferred, call functions with implicit
arguments which will be inferred as well, extend the syntax with
notations, factorize branches when pattern-matching, etc.  In this
chapter, we present these language extensions and we give some
explanations on how this language is translated down to the core
language presented in the :ref:`previous chapter <core-language>`.

.. toctree::
   :maxdepth: 1

   .. The two chapters at the top and the bottom (Gallina extensions
      and Vernacular commands) are planned for removal.  Eventually,
      the present "Language extensions" chapter will play the role of
      the former Gallina extensions chapter.

   ../gallina-extensions

   .. The order of the sections in this chapter is not really thought
      through.

   .. The sub-section about canonical structures is to be removed from
      the implicit arguments section and moved to the canonical
      structure section below.

   implicit-arguments

   .. To be consolidated with the section about extended pattern
      matching from the Gallina extensions chapter:

   ../../addendum/extended-pattern-matching
   ../../user-extensions/syntax-extensions

   .. To be consolidated with the section about implicit coercions
      from the Gallina extensions chapter:

   ../../addendum/implicit-coercions

   ../../addendum/type-classes

   .. To be consolidated with the sub-section about canonical
      structures from the implicit arguments section:

   ../../addendum/canonical-structures

   ../../addendum/program

   .. Some parts (queries) to be moved to the "Using" part?  The rest
      to be spread around.

   ../../proof-engine/vernacular-commands
