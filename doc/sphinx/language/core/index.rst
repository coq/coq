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

   .. The two chapters Gallina specification language and CIC are
      planned for removal.  Eventually, the present "Core language"
      chapter will play the role of the former Gallina chapter, except
      that some core notions will have moved there from the former
      Gallina extensions chapter.

   ../gallina-specification-language
   ../cic

   .. Comments are used to show upcoming sections (not yet split out).

   .. Lexical conventions, how to read the grammars in the manual,
      presentations of the basic notions: terms, commands, tactics,
      attributes and options.

   .. Terms, typing and conversion (only basic constructs:
      abstraction, product, application, type cast, brief mention of
      sorts).

   .. Assumptions

   .. Definitions (vernac) and local definitions (let in).  Includes
      opaque definitions and a brief introduction to the interactive
      proof mode, in the spirit of CEP #42.

   .. Variants and the match-construct

   records

   .. Inductive types and recursive definitions (Inductive, fix and
      Fixpoint)

   .. Co-inductive types and co-recursive definitions (CoInductive,
      cofix and CoFixpoint)

   .. Conversion (including fast reduction machines)

   .. Native integers and floats (and arrays when they arrive).  Here
      or in the Libraries chapter or merged with the section on
      conversion above?

   .. The next section would be about sorts, would include the current
      addendum chapter about SProp, but also explain clearly
      Set and Prop, imprecativity, the -imprecative-set option.

   ../../addendum/sprop

   .. The next section would be about universes, including how to
      manipulate them explicitly, and template polymorphism.  It would
      include the current addendum chapter about full universe
      polymorphism.

   ../../addendum/universe-polymorphism

   sections

   .. The next section would be everything about modules, including
      the grammar from the Gallina extensions chapter and the typing
      rules from the modules chapter.  It would probably also include
      everything about library files, including what is currently in
      the Gallina extensions chapter and the Vernacular commands
      chapter (unless this rather goes to the "Using" part).

   ../module-system
