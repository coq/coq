.. attr:: deprecated ( {? since = @string , } {? note = @string } )
   :name: deprecated

    At least one of :n:`since` or :n:`note` must be present.  If both are present,
    either one may appear first and they must be separated by a comma.

    This attribute is supported by the following commands: :cmd:`Ltac`,
    :cmd:`Tactic Notation`, :cmd:`Notation`, :cmd:`Infix`.

    It can trigger the following warnings:

    .. warn:: Tactic @qualid is deprecated since @string__since. @string__note.
              Tactic Notation @qualid is deprecated since @string__since. @string__note.
              Notation @string is deprecated since @string__since. @string__note.

       :n:`@qualid` or :n:`@string` is the notation, :n:`@string__since` is the version number,
       :n:`@string__note` is the note (usually explains the replacement).

    .. example::

       .. coqtop:: all reset warn

          #[deprecated(since="8.9.0", note="Use idtac instead.")]
          Ltac foo := idtac.

          Goal True.
          Proof.
          now foo.
          Abort.
