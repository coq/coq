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
  to the ML language family, Mtac2 reuses the language of Rocq itself
  as the language to build Rocq tactics.

- `Coq-Elpi <https://github.com/LPCIC/coq-elpi>`_ is an external plugin
  which provides an extension language based on λProlog, a programming
  language well suited to write code which manipulates syntax trees with
  binders such as Rocq terms.
  Elpi provides an extensive set of APIs to create commands (i.e. script
  the vernacular language) and tactics.

- The most traditional way of building new complex tactics is to write
  a Rocq plugin in OCaml. Beware that this requires much more
  effort. Furthermore, Rocq's OCaml API can change from release
  to release without backward compatibility support, which can cause
  a significant ongoing maintenance burden.
  A tutorial for writing Rocq plugins is available in the Rocq
  repository in `doc/plugin_tutorial
  <https://github.com/coq/coq/tree/master/doc/plugin_tutorial>`_.

.. toctree::
   :maxdepth: 1

   ../../proof-engine/ltac
   ../../proof-engine/ltac2
