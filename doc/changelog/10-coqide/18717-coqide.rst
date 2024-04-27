- **Changed:**
  The default key binding modifier for the Navigation menu
  was changed to Alt on non-macOS systems.  The previous default,
  Ctrl, hid some conventional cursor movement bindings such as Ctrl-Left,
  Ctrl-Right, Ctrl-Home and Ctrl-End.  The new default generally
  has no effect if you've previously installed Coq on your
  system.  See :ref:`Shortcuts<shortcuts>` to change the default.

  The Edit/Undo key binding was changed from Ctrl-U to Ctrl-Z to
  be more consistent with common conventions.  `View/Previous Tab`
  and `View/Next Tab` were changed from `Alt-Left/Right` to
  `Ctrl-PgUp/PgDn` (`Cmd-PgUp/PgDn` on macOS).  To change key
  bindings on your system (e.g. back to Ctrl-U), see :ref:`key_bindings`
  (`#18717 <https://github.com/coq/coq/pull/18717>`_,
  by Sylvain Chiron).
- **Changed:**
  Changing modifiers for the View menu only applies
  to toggleable items; View/Show Proof was changed to Shift-F2
  (`#18717 <https://github.com/coq/coq/pull/18717>`_,
  by Sylvain Chiron).
- **Added:**
  Edit/Select All and Navigation/Fully Check menu items
  (`#18717 <https://github.com/coq/coq/pull/18717>`_,
  fixes `#16141 <https://github.com/coq/coq/issues/16141>`_,
  by Sylvain Chiron).
