# CoqIDE FAQ #

### What is CoqIDE?

A powerful GTK3-based graphical interface for Coq.
See https://coq.inria.fr for more information.

### How to enable Emacs keybindings?

Insert the following line in your `gtkrc` file:
```
gtk-key-theme-name = "Emacs"
```
The location of this file is system-dependent. If you're running
GNOME, you may use the graphical configuration tools.

See also the µPG mode in CoqIDE preferences and help.

### How to use those Forall (∀) and Exists (∃) pretty symbols?

Thanks to the Notation features in Coq, you just need to insert these
lines in your Coq Buffer :
```
Notation "∀ x : t, P" := (forall x:t, P) (at level 200, x ident).
Notation "∃ x : t, P" := (exists x:t, P) (at level 200, x ident).
```
You need to load a file containing these lines or to enter the `∀`
using an input method (see next question below).
To try it, just use `Require Import Utf8` from inside CoqIDE.

To enable these notations automatically, start `coqide` with:
```
coqide -ri Utf8
```

### How to type non-ASCII symbols?

There are several methods, some of which are described below.

#### Type the unicode code point

The hexadecimal unicode code point of ∀ is 2200 and the one of ∃ is 2203.
[This Wikipedia page](https://en.wikipedia.org/wiki/Unicode_input#Hexadecimal_input)
explains how to generate a character from its code point in different systems.
For instance, under Linux, you must press Ctrl-Shift-U, then type the code point,
then press Enter.

See https://unicode.org for more code points.

#### Use the LaTeX-to-unicode feature of CoqIDE

You can type e.g. `\forall` or `\exists` in your buffer,
then (while the cursor is at the end of the word)
select *Tools > LaTeX-to-unicode* (or, equivalently, type Shift-Space).

#### Use an input method editor

Such editors include SCIM and iBus. The latter offers
a module for LaTeX-like inputting.

### What encoding should I use?

The encoding option is related to the way files are saved.
CoqIDE can support any encoding if you type its name in the preferences,
but Coq only supports UTF-8. Therefore, do keep the encoding
as UTF-8 until it becomes important for you to exchange files
with non-UTF-8-aware applications.
