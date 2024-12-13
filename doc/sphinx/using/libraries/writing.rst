Writing Rocq libraries and plugins
===================================

This section presents the part of the Rocq language that is useful only
to library and plugin authors.  A tutorial for writing Rocq plugins is
available in the Rocq repository in `doc/plugin_tutorial
<https://github.com/coq/coq/tree/master/doc/plugin_tutorial>`_.

Deprecating library objects, tactics or library files
-----------------------------------------------------

You may use the following :term:`attribute` to deprecate a notation,
tactic, definition, axiom, theorem or file.  When renaming a definition or theorem, you can introduce a
deprecated compatibility alias using :cmd:`Notation (abbreviation)`
(see :ref:`the example below <compatibility-alias>`).

.. attr:: deprecated ( {? since = @string , } {? note = @string , } {? use = @qualid } )
   :name: deprecated

   At least one of :n:`since` or :n:`note` must be present.  If both
   are present, either one may appear first and they must be separated
   by a comma. If they are present, they will be used in the warning
   message, and :n:`since` will also be used in the warning name and
   categories. Spaces inside :n:`since` are changed to hyphens.

   This attribute is supported by the following commands: :cmd:`Ltac`,
   :cmd:`Tactic Notation`, :cmd:`Notation`, :cmd:`Infix`, :cmd:`Ltac2`,
   :cmd:`Ltac2 Notation`, :cmd:`Ltac2 external`, :cmd:`Definition`,
   :cmd:`Theorem`, and similar commands. To attach it to a
   compiled library file, use :cmd:`Attributes`.

   The :n:`use` attribute can be used for commands such as :cmd:`Definition`,
   :cmd:`Theorem`, and ``Notation @ident``. Its value must refer to an
   existing constant of abbreviation and is printed as part of the warning
   message as well as used by LSP based user interfaces as a quick fix.

   It can trigger the following warnings:

   .. warn:: Library File @qualid is deprecated since @string__since. @string__note. Use @qualid__use instead.
             Library File (transitively required) @qualid is deprecated since @string__since. @string__note. Use @qualid__use instead.
             Ltac2 alias @qualid is deprecated since @string__since. @string__note.
             Ltac2 definition @qualid is deprecated since @string__since. @string__note.
             Ltac2 notation {+ @ltac2_scope } is deprecated since @string__since. @string__note.
             Ltac2 constructor @qualid is deprecated since @string__since. @string__note.
             Notation @string is deprecated since @string__since. @string__note. Use @qualid__use instead.
             Tactic @qualid is deprecated since @string__since. @string__note.
             Tactic Notation @qualid is deprecated since @string__since. @string__note.

      :n:`@qualid` or :n:`@string` is the notation,
      :n:`@string__since` is the version number, :n:`@string__note` is
      the note (usually explains the replacement).

      Explicitly :cmd:`Require`\ing a file that has been deprecated,
      using the :cmd:`Attributes` command, triggers a ``Library File``
      deprecation warning. Requiring a deprecated file, even indirectly through a chain of
      :cmd:`Require`\s, will produce a
      ``Library File (transitively required)`` deprecation warning
      if the :opt:`Warnings` option "deprecated-transitive-library-file"
      is set (it is "-deprecated-transitive-library-file" by default, silencing the warning).

.. note::

   Rocq and its standard library follow this deprecation policy:

   * it should always be possible for a project written in Rocq to be
     compatible with two successive major versions,
   * features must be deprecated in one major version before removal,
   * Rocq developers should provide an estimate of the required effort
     to fix a project with respect to a given change,
   * breaking changes should be clearly documented in the public
     release notes, along with recommendations on how to fix a project
     if it breaks.

   See :cite:`Zimmermann19`, Section 3.6.3, for more details.

Triggering warning for library objects or library files
-------------------------------------------------------

You may use the following :term:`attribute` to trigger a warning on a
notation, definition, axiom, theorem or file.

.. attr:: warn ( note = @string , {? cats = @string } )
   :name: warn

   The :n:`note` field will be used as the warning message, and
   :n:`cats` is a comma separated list of categories to be used in the
   warning name and categories. Leading and trailing spaces in each
   category are trimmed, whereas internal spaces are changed to
   hyphens. If both :n:`note` and :n:`cats` are present, either one
   may appear first and they must be separated by a comma.

   This attribute is supported by the following commands:
   :cmd:`Notation`, :cmd:`Infix`, :cmd:`Definition`, :cmd:`Theorem`,
   and similar commands. To attach it to a compiled library file, use
   :cmd:`Attributes`.

   It can trigger the following warning:

   .. warn:: @string__note

      :n:`@string__note` is the note. It's common practice to start it
      with a capital and end it with a period.

      Explicitly :cmd:`Require`\ing a file that has a warn message set
      using the :cmd:`Attributes` command, triggers a
      ``warn-library-file`` warning. Requiring such a file, even
      indirectly through a chain of :cmd:`Require`\s, will produce a
      ``warn-transitive-library-file`` warning if the :opt:`Warnings`
      option "warn-transitive-library-file" is set (it is
      "-warn-transitive-library-file" by default, silencing the
      warning).

.. example:: Deprecating a tactic.

   .. rocqtop:: all abort warn

      #[deprecated(since="mylib 0.9", note="Use idtac instead.")]
      Ltac foo := idtac.
      Goal True.
      Proof.
      now foo.

.. _compatibility-alias:

.. example:: Introducing a compatibility alias

   Let's say your library initially contained:

   .. rocqtop:: in

      Definition foo x := S x.

   and you want to rename `foo` into `bar`, but you want to avoid breaking
   your users' code without advanced notice.  To do so, replace the previous
   code by the following:

   .. rocqtop:: in reset

      Definition bar x := S x.
      #[deprecated(since="mylib 1.2", note="Use bar instead.")]
      Notation foo := bar (only parsing).

   Then, the following code still works, but emits a warning:

   .. rocqtop:: all warn

      Check (foo 0).
