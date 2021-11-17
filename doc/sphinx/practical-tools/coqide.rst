.. |GtkSourceView| replace:: :smallcaps:`GtkSourceView`

.. _coqintegrateddevelopmentenvironment:

Coq Integrated Development Environment
========================================

The Coq Integrated Development Environment is a graphical tool, to be
used as a user-friendly replacement to `coqtop`. Its main purpose is to
allow the user to navigate forward and backward into a Coq
file, executing corresponding commands or undoing them respectively.

CoqIDE is run by typing the command `coqide` on the command line.
Without argument, the main screen is displayed with an “unnamed
buffer”, and with a filename as argument, another buffer displaying
the contents of that file. Additionally, `coqide` accepts the same
options as `coqtop`, given in :ref:`thecoqcommands`, the ones having obviously
no meaning for CoqIDE being ignored.

.. _coqide_mainscreen:

  .. image:: ../_static/coqide.png
     :alt: CoqIDE main screen

A sample CoqIDE main screen, while navigating into a file `Fermat.v`,
is shown in the figure :ref:`CoqIDE main screen <coqide_mainscreen>`.
At the top is a menu bar, and a tool bar
below it. The large window on the left is displaying the various
*script buffers*. The upper right window is the *goal window*, where
goals to be proven are displayed. The lower right window is the *message
window*, where various messages resulting from commands are displayed.
At the bottom is the status bar.

Managing files and buffers, basic editing
----------------------------------------------

In the script window, you may open arbitrarily many buffers to edit.
The *File* menu allows you to open files or create some, save them,
print or export them into various formats. Among all these buffers,
there is always one which is the current *running buffer*, whose name
is displayed on a background in the *processed* color (green by default), which
is the one where Coq commands are currently executed.

Buffers may be edited as in any text editor, and classical basic
editing commands (Copy/Paste, …) are available in the *Edit* menu.
CoqIDE offers only basic editing commands, so if you need more complex
editing commands, you may launch your favorite text editor on the
current buffer, using the *Edit/External Editor* menu.

Interactive navigation into Coq scripts
--------------------------------------------

The running buffer is the one where navigation takes place. The toolbar offers
five basic commands for this. The first one, represented by a down arrow icon,
is for going forward executing one command. If that command is successful, the
part of the script that has been executed is displayed on a background with the
processed color. If that command fails, the error message is displayed in the
message window, and the location of the error is emphasized by an underline in
the error foreground color (red by default).

In the figure :ref:`CoqIDE main screen <coqide_mainscreen>`,
the running buffer is `Fermat.v`, all commands until
the ``Theorem`` have been already executed, and the user tried to go
forward executing ``Induction n``. That command failed because no such
tactic exists (names of standard tactics are written in lowercase),
and the failing command is underlined.

Notice that the processed part of the running buffer is not editable. If
you ever want to modify something you have to go backward using the up
arrow tool, or even better, put the cursor where you want to go back
and use the goto button. Unlike with `coqtop`, you should never use
``Undo`` to go backward.

There are two additional buttons for navigation within the running buffer. The
"down" button with a line goes directly to the end; the "up" button with a line
goes back to the beginning. The handling of errors when using the go-to-the-end
button depends on whether Coq is running in asynchronous mode or not (see
Chapter :ref:`asynchronousandparallelproofprocessing`). If it is not running in that mode, execution
stops as soon as an error is found. Otherwise, execution continues, and the
error is marked with an underline in the error foreground color, with a
background in the error background color (pink by default). The same
characterization of error-handling applies when running several commands using
the "goto" button.

If you ever try to execute a command that runs for a long time
and would like to abort it before it terminates, you may
use the interrupt button (the white cross on a red circle).

There are other buttons on the CoqIDE toolbar: a button to save the running
buffer; a button to close the current buffer (an "X"); buttons to switch among
buffers (left and right arrows); an "information" button; and a "gears" button.

The "gears" button submits proof terms to the Coq kernel for type checking.
When Coq uses asynchronous processing (see Chapter :ref:`asynchronousandparallelproofprocessing`),
proofs may have been completed without kernel-checking of generated proof terms.
The presence of unchecked proof terms is indicated by ``Qed`` statements that
have a subdued *being-processed* color (light blue by default), rather than the
processed color, though their preceding proofs have the processed color.

Notice that for all these buttons, except for the "gears" button, their operations
are also available in the menu, where their keyboard shortcuts are given.

Commands and templates
----------------------

The Templates menu allows using shortcuts to insert
commands. This is a nice way to proceed if you are not sure of the
syntax of the command you want.

Moreover, from this menu you can automatically insert templates of complex
commands like ``Fixpoint`` that you can conveniently fill afterwards.

Queries
------------

.. image:: ../_static/coqide-queries.png
   :alt: CoqIDE queries

We call *query* any command that does not change the current state,
such as ``Check``, ``Search``, etc. To run such commands interactively, without
writing them in scripts, CoqIDE offers a *query pane*. The query pane can be
displayed on demand by using the ``View`` menu, or using the shortcut ``F1``.
Queries can also be performed by selecting a particular phrase, then choosing an
item from the ``Queries`` menu. The response then appears in the message window.
The image above shows the result after selecting of the phrase
``Nat.mul`` in the script window, and choosing ``Print`` from the ``Queries``
menu.


Compilation
----------------

The `Compile` menu offers direct commands to:

+ compile the current buffer
+ run a compilation using `make`
+ go to the last compilation error
+ create a `Makefile` using `coq_makefile`.

Customizations
-------------------

You may customize your environment using the menu Edit/Preferences. A new
window will be displayed, with several customization sections
presented as a notebook.

The first section is for selecting the text font used for scripts,
goal and message windows.

The second and third sections are for controlling colors and style of
the three main buffers. A predefined Coq highlighting style as well
as standard |GtkSourceView| styles are available. Other styles can be
added e.g. in ``$HOME/.local/share/gtksourceview-3.0/styles/`` (see
the general documentation about |GtkSourceView| for the various
possibilities). Note that the style of the rest of graphical part of
CoqIDE is not under the control of |GtkSourceView| but of GTK+ and
governed by files such as ``settings.ini`` and ``gtk.css`` in
``$XDG_CONFIG_HOME/gtk-3.0`` or files in
``$HOME/.themes/NameOfTheme/gtk-3.0``, as well as the environment
variable ``GTK_THEME`` (search on internet for the various
possibilities).

The fourth section is for customizing the editor. It includes in
particular the ability to activate an Emacs mode named
micro-Proof-General (use the Help menu to know more about the
available bindings).

The next section is devoted to file management: you may configure
automatic saving of files, by periodically saving the contents into
files named `#f#` for each opened file `f`. You may also activate the
*revert* feature: in case a opened file is modified on the disk by a
third party, CoqIDE may read it again for you. Note that in the case
you edited that same file, you will be prompted to choose to either
discard your changes or not. The File charset encoding choice is
described below in :ref:`character-encoding-saved-files`.

The `Externals` section allows customizing the external commands for
compilation, printing, web browsing. In the browser command, you may
use `%s` to denote the URL to open, for example:
`firefox -remote "OpenURL(%s)"`.

Notice that these settings are saved in the file ``coqiderc`` in the
``coq`` subdirectory of the user configuration directory which
is the value of ``$XDG_CONFIG_HOME`` if this environment variable is
set and which otherwise is ``$HOME/.config/``.

A GTK+ accelerator keymap is saved under the name ``coqide.keys`` in
the same ``coq`` subdirectory of the user configuration directory. It
is not recommended to edit this file manually: to modify a given menu
shortcut, go to the corresponding menu item without releasing the
mouse button, press the key you want for the new shortcut, and release
the mouse button afterwards. If your system does not allow it, you may
still edit this configuration file by hand, but this is more involved.


Using Unicode symbols
--------------------------

CoqIDE is based on GTK+ and inherits from it support for Unicode in
its text windows. Consequently a large set of symbols is available for
notations. Furthermore, CoqIDE conveniently provides a simple way to
input Unicode characters.


Displaying Unicode symbols
~~~~~~~~~~~~~~~~~~~~~~~~~~

You just need to define suitable notations as described in the chapter
:ref:`syntax-extensions-and-notation-scopes`. For example, to use the
mathematical symbols ∀ and ∃, you may define:

.. coqtop:: in

   Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
     (at level 200, x binder, y binder, right associativity)
     : type_scope.
   Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
     (at level 200, x binder, y binder, right associativity)
     : type_scope.

There exists a small set of such notations already defined, in the
file `utf8.v` of Coq library, so you may enable them just by
``Require Import Unicode.Utf8`` inside CoqIDE, or equivalently,
by starting CoqIDE with ``coqide -l utf8``.

However, there are some issues when using such Unicode symbols: you of
course need to use a character font which supports them. In the Fonts
section of the preferences, the Preview line displays some Unicode
symbols, so you could figure out if the selected font is OK. Related
to this, one thing you may need to do is choosing whether GTK+ should
use antialiased fonts or not, by setting the environment variable
`GDK_USE_XFT` to 1 or 0 respectively.


.. _coqide-unicode:

Bindings for input of Unicode symbols
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CoqIDE supports a builtin mechanism to input non-ASCII symbols.
For example, to input ``π``, it suffices to type ``\pi`` then press the
combination of key ``Shift+Space`` (default key binding). Often, it
suffices to type a prefix of the latex token, e.g. typing ``\p``
then ``Shift+Space`` suffices to insert a ``π``.

For several symbols, ASCII art is also recognized, e.g. ``\->`` for a
right arrow, or ``\>=`` for a greater than or equal sign.

A larger number of latex tokens are supported by default. The full list
is available here:
https://github.com/coq/coq/blob/master/ide/coqide/default_bindings_src.ml

Custom bindings may be added, as explained further on.

The mechanism is active by default, but can be turned off in the Editor section
of the preferences.

.. note::

    It remains possible to input non-ASCII symbols using system-wide
    approaches independent of CoqIDE.


Adding custom bindings
~~~~~~~~~~~~~~~~~~~~~~

To extend the default set of bindings, create a file named ``coqide.bindings``
and place it in the same folder as ``coqide.keys``. This would be
the folder ``$XDG_CONFIG_HOME/coq``, defaulting to ``~/.config/coq``
if ``XDG_CONFIG_HOME`` is unset. The file `coqide.bindings` should contain one
binding per line, in the form ``\key value``, followed by an optional priority
integer. (The key and value should not contain any space character.)

.. example::

   Here is an example configuration file:

   ::

     \par ||
     \pi π 1
     \le ≤ 1
     \lambda λ 2
     \lambdas λs

Above, the priority number 1 on ``\pi`` indicates that the prefix ``\p``
should resolve to ``\pi``, and not to something else (e.g. ``\par``).
Similarly, the above settings ensure than ``\l`` resolves to ``\le``,
and that ``\la`` resolves to ``\lambda``.

It can be useful to work with per-project binding files. For this purpose
CoqIDE accepts a command line argument of the form
``-unicode-bindings file1,file2,...,fileN``.
Each of the file tokens provided may consists of one of:

 -  a path to a custom bindings file,
 -  the token ``default``, which resolves to the default bindings file,
 -  the token ``local``, which resolves to the `coqide.bindings` file
    stored in the user configuration directory.

.. warning::

   If a filename other than the first one includes a "~" to refer
   to the home directory, it won't be expanded properly. To work around that
   issue, one should not use comas but instead repeat the flag, in the form:
   ``-unicode-bindings file1 .. -unicode-bindings fileN``.

.. note::

   If two bindings for a same token both have the same priority value
   (or both have no priority value set), then the binding considered is
   the one from the file that comes first on the command line.


.. _character-encoding-saved-files:

Character encoding for saved files
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the Files section of the preferences, the encoding option is
related to the way files are saved.

If you have no need to exchange files with non-UTF-8 aware
applications, it is better to choose the UTF-8 encoding, since it
guarantees that your files will be read again without problems. (This
is because when CoqIDE reads a file, it tries to automatically detect
its character encoding.)

If you choose something else than UTF-8, then missing characters will
be written encoded by `\x{....}` or `\x{........}` where each dot is
an hexadecimal digit: the number between braces is the hexadecimal
Unicode index for the missing character.

.. _coqide-debugger:

Debugger
--------

Version 8.15 introduces a visual debugger for |Ltac| tactics within
CoqIDE.  It supports setting breakpoints visually and automatically
displaying the stopping point in the source code with "continue",
"step over" "step in" and "step out" operations.  The call stack and variable
values for each stack frame are shown in a new panel.

The debugger is based on the non-visual |Ltac| :ref:`debugger <interactive-debugger>`.
We'd like to eventually support other scripting facilities such as Ltac2.

Since the visual debugger is new in 8.15, you may encounter bugs or usability issues.
The behavior and user interface will evolve as the debugger is refined.
There are notes on bugs and potential enhancements at the end of
`this page <https://github.com/coq/coq/wiki/Ltac-Debugger-Preview>`_.
Feel free to suggest changes and improvements by opening an issue on
`GitHub <https://github.com/coq/coq/issues/new>`_, or contact `@jfehrle`
directly through email, Zulip or Discourse.

Breakpoints
~~~~~~~~~~~

This screenshot shows the debugger stopped at a breakpoint in the |Ltac| tactic
`my_tac`.  Breakpoints are shown with a red background and the stopping point is
shown with a dark blue background.  `Set Ltac Debug.` enables stopping in the
debugger.

  .. image:: ../_static/debugger.png
     :alt: CoqIDE Debugger

  .. created with:
     Set Ltac Debug.  (* enable the debugger *)

     Ltac my_tac c :=
       let con := constr:(forall a b : nat,
         (a + b) * c = a * c + b * c) in
       idtac "A"; idtac "B"; idtac "C".

     Goal True.
     my_tac 2.

You can control the debugger with function and control keys.  Some
messages are shown in the Messages panel.  You can type
:ref:`debugger commands <interactive-debugger>`
in that panel when it shows the debug prompt.

The script is not editable while Coq is processing tactics or stopped
in the debugger.  When Coq is stopped in the debugger (e.g., at a breakpoint),
the blue segment in the "in progress" slider at the bottom edge of the window
will be stopped at the left hand edge of its range.

The function keys are listed, for the moment, with one exception, in the `Debug` menu:

Toggle breakpoint (F8)
  Position the cursor on the first character of the tactic name in an Ltac
  construct, then press F8.  Press again to remove the breakpoint.  F8 is
  accepted only when all of the coqtop sessions are idle (i.e. at the debug
  prompt or not processing a tactic or command).

  Note that :term:`sentences <sentence>` containing a single built-in tactic
  are not Ltac constructs.  A breakpoint on :n:`intros.`, for example, is
  ignored, while breakpoints on either tactic in :n:`intros; idtac.` work.
  A breakpoint on, say, :n:`my_ltac_tactic.` also works.

  Breakpoints on Ltac :n:`@value_tactic`\s, which compute values without changing
  the proof context, such as :tacn:`eval`, are ignored.

  You must set at least one breakpoint in order to enter the debugger.

Continue (F9)
  Continue processing the proof.  If you're not stopped in the debugger, this is
  equivalent to "Run to end" (Control End).

Step over (Control ↓)
  When stopped in the debugger,
  execute the next tactic without stopping inside it.  If the debugger reaches
  a breakpoint in the tactic, it will stop.  This is the same key combination used
  for "Forward one command"—if you're stopped in the debugger then it does a "Step over"
  and otherwise it does a "Forward".  Combining the two functions makes it easy
  to step through a script in a natural way when some breakpoints are set.

Step in (F10)
  When stopped in the debugger, if next tactic is an |Ltac| tactic, stop at the
  first possible point in the tactic.  Otherwise acts as a "step over".

Step out (Shift F10)
  When stopped in the debugger, continue and then
  stop at the first possible point after exiting the current |Ltac| tactic.  If the
  debugger reaches a breakpoint in the tactic, it will stop.

Break (F11)
  Stops the debugger at the next possible stopping point, from which you can
  step or continue.   (Not supported in Windows at this time.)

If you step through `idtac "A"; idtac "B"; idtac "C".`, you'll notice that the
steps for `my_tac` are:

  | `idtac "A"; idtac "B"; idtac "C"`
  | `idtac "A"; idtac "B"`
  | `idtac "A"`
  | `idtac "B"`
  | `idtac "C"`

which reflects the two-phase execution process for the :n:`@tactic ; @tactic`
construct.

Also keep in mind that |Ltac| backtracking may cause the call stack to revert to
a previous state.  This may cause confusion.  Currently there's no special
indication that this has happened.

.. unfortunately not working:
   Note: This `Wiki page <https://github.com/coq/coq/wiki/Configuration-of-CoqIDE#the-alternative-set-of-bindings>`_
   describes a way to change CoqIDE key bindings.

Call Stack and Variables
~~~~~~~~~~~~~~~~~~~~~~~~

The bottom panel shows the call stack and the variables defined for the selected
stack frame.  Stack frames normally show the name of tactic being executed, the line
number and the last component of the filename without the :n:`.v` suffix.
The directory part of the module name is shown when the frame is not in
the toplevel script file.  For example,
:n:`make_rewriter:387, AllTactics (Rewriter.Rewriter)` refers to the file
with the module name :n:`Rewriter.Rewriter.AllTactics`.

Note: A few stack frames aren't yet displayed in this described format (e.g. those starting
with :n:`???`) and may be extraneous. In some cases, the tactic name is not shown.

Click on a stack frame or press the Up (↑) or Down (↓) keys to select a
stack frame.  Coq will jump to the associated code and display the variables for that stack
frame.  You can select text with the mouse and then copy it to the clipboard with
Control-C.  Control-A selects the entire stack.

The variables panel uses a tree control to show variables defined in the selected
stack frame.  To see values that don't fit on a single line, click on the triangle.
You can select one or more entries from the tree in the usual way by
clicking, shift-clicking and control-clicking on an entry.  Control-A selects
all entries.  Control-C copies the selected entries to the clipboard.

Note: Some variable are not displayed in a useful form.  For example, the value
shown for :n:`tac` in a script containing :n:`let tac = ltac:(auto)` appears
only as :n:`<genarg:tacvalue>`.  We hope to address this soon.

The :n:`DETACH` button moves the debugger panel into a separate window, which
will make it easier to examine its contents.

Supported use cases
~~~~~~~~~~~~~~~~~~~

There are two main use cases for the debugger.  They're not very compatible.
Instead of showing warning messages or forcing the user to explicitly pick one
mode or another, for now it's up to the user to know the limitations and work within them.

The *single file* case is running the debugger on a single *primary* script without ever
stopping in other *secondary* scripts.  In this case, you can edit the primary script while
Coq is not running it nor stopped in the debugger.  The position of breakpoints will be updated
automatically as you edit the file.  It's fine to run the debugger in multiple buffers--you will not
be confused.  The single-file case is preferable when you can use it.

The *multi-file* case is when a primary script stops in a secondary script.  In this
case, breakpoints in the secondary script that move due to script editing may no longer
match the locations in the compiled secondary script.  The debugger won't stop at these
breakpoints as you expect.  Also, the code highlighted for stack frames in that
script may be incorrect.  You will need to re-compile
the secondary script and then restart the primary script (Restart, Ctrl-HOME) to get back
to a consistent state.

For multi-file debugging, we suggest detaching the Messages, Proof Context
and Debugger panels so they are
in separate windows.  To do so, click on the arrow icon next to "Messages",
select "Windows / Detach Proof" from the menu and click on "DETACH" in the
Debugger panel.  Note that the Debugger panel is initially attached to
the Script panel of the toplevel script.  Also note that, for now, the
"in progress" slider is accurate only when the associated toplevel script panel
is visible.


If a debugger instance is stopped in a secondary script, the debugger function
keys are directed to the debugger instance associated with the primary script.
The debugger doesn't attempt to support multiple instances
stopped in the same secondary script.  If you have a need to do this, run
each debugger instance in a separate CoqIDE process/window.

Note that if you set a breakpoint in a script that may be called by multiple debugger
instances, you may inadvertently find you've gotten into unsupported territory.
