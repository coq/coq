
DESCRIPTION:

An emacs mode to help editing Coq vernacular files.

AUTHOR:

Jean-Christophe Filliatre (jcfillia@lri.fr),
	from the Caml mode of Xavier Leroy.

CONTENTS:

    gallina.el     A major mode for editing Coq files in Gnu Emacs

USAGE:

Add the following lines to your .emacs file:

(setq auto-mode-alist (cons '("\\.v$" . coq-mode) auto-mode-alist))
(autoload 'coq-mode "gallina" "Major mode for editing Coq vernacular." t)

The Coq major mode is triggered by visiting a file with extension .v,
or manually by M-x coq-mode. It gives you the correct syntax table for
the Coq language, and also a rudimentary indentation facility:

- pressing TAB at the beginning of a line indents the line like the line above

- extra TABs increase the indentation level (by 2 spaces by default)

- M-TAB decreases the indentation level.

