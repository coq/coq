`#17421 <https://github.com/coq/coq/pull/17421>`_, by Sylvain Chiron:
- **Changed:**
  - Some default key bindings were changed, notably Alt
    is now the default modifier for navigation (except on macOS)
    just like with VsCoq.
  - Changing modifiers for the View menu only applies
    to togglable items.
  - The default browser command for Linux now uses `xdg-open`.
  - Find/replace UI was improved: margins, icons for found/not found
    (fixes `#11024 <https://github.com/coq/coq/issues/11024>`_).
- **Fixed:**
  - Loading dropped files whose name contains special characters
    (fixes `#3977 <https://github.com/coq/coq/issues/3977>`_).
  - “Zoom fit” feature, which didn’t work.
  - Changing document tabs position no longer needs a restart.
- **Added:**
  - Document tabs are now reorderable.
  - “Select All” menu item in the Edit menu
    (fixes `#16141 <https://github.com/coq/coq/issues/16141>`_).
