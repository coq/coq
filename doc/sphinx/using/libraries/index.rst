.. _libraries:

=====================
Libraries and plugins
=====================

Libraries and plugins contain compiled Coq scripts with useful definitions,
theorems, notations and settings that can be loaded at runtime.  In addition,
plugins can add new tactics and commands written in OCaml.

Coq is distributed with a standard library and a set of internal
plugins (most of which provide tactics that have already been
presented in :ref:`writing-proofs`).  This chapter presents this
standard library and some of these internal plugins which provide
features that are not tactics.

In addition, Coq has a rich ecosystem of external libraries and
plugins.  These libraries and plugins can be browsed online through
the `Coq Package Index <https://coq.inria.fr/opam/www/>`_ and
installed with the `opam package manager
<https://coq.inria.fr/opam-using.html>`_.

:gdef:`Libraries <library>` contain only compiled Coq scripts.
:gdef:`Plugins <plugin>` can also include compiled OCaml code that can change
the behavior of Coq.  Both are :term:`packages <package>`.
While users configure and load them identically, there are a few differences
to consider:

- Nearly all plugins add functionality that could not be added otherwise
  and they likely add new top-level commands or tactics.
- Compared to libraries, plugins can change Coq's behavior in many possibly
  unexpected ways. Therefore, using a plugin requires a higher degree of trust
  in its authors than is needed for libraries.  If desired, you can mitigate
  trust issues by running :ref:`coqchk` on compiled files produced from Coq
  scripts that load plugins.  (`coqchk` doesn't load plugins, so they won't be
  part of trusted code base.)
- Plugins that aren't in Coq's
  `CI (continuous integration) system <https://github.com/coq/coq/blob/master/dev/ci/README-users.md>`_
  are more likely
  to break across major versions due to source code changes to Coq.  You may want to
  consider this before adopting a new plugin for your project.

.. toctree::
   :maxdepth: 1

   ../../language/coq-library
   ../../addendum/extraction
   ../../addendum/miscellaneous-extensions
   funind
   writing
