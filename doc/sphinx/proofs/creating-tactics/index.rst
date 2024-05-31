.. _writing-tactics:

====================
Creating new tactics
====================

The languages presented in this chapter allow one to build complex
tactics by combining existing ones with constructs such as
conditionals and looping.  While :ref:`Ltac <ltac>` was initially
thought of as a language for doing some basic combinations, it has
been used successfully to build highly complex tactics as well, but
this has also highlighted its limits and fragility.  The
language :ref:`Ltac2 <ltac2>` is a typed and more principled variant
which is more adapted to building complex tactics.

There are other solutions beyond these two tactic languages to write
new tactics:

- `Mtac2 <https://github.com/Mtac2/Mtac2>`_ is an external plugin
  which provides another typed tactic language.  While Ltac2 belongs
  to the ML language family, Mtac2 reuses the language of Coq itself
  as the language to build Coq tactics.

- `Coq-Elpi <https://github.com/LPCIC/coq-elpi>`_ is an external plugin
  which provides an extension language based on λProlog, a programming
  language well suited to write code which manipulates syntax trees with
  binders such as Coq terms.
  Elpi provides an extensive set of APIs to create commands (i.e. script
  the vernacular language) and tactics.

- The most traditional way of building new complex tactics is to write
  a Coq plugin in OCaml.  Beware that this also requires much more
  effort and commitment.  A tutorial for writing Coq plugins is
  available in the Coq repository in `doc/plugin_tutorial
  <https://github.com/coq/coq/tree/master/doc/plugin_tutorial>`_.

.. toctree::
   :maxdepth: 1

   ../../proof-engine/ltac
   ../../proof-engine/ltac2
