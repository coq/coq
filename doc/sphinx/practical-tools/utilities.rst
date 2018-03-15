\chapter[Utilities]{Utilities\label{Utilities}}
%HEVEA\cutname{tools.html}

The distribution provides utilities to simplify some tedious works
beside proof development, tactics writing or documentation.

\section[Using Coq as a library]{Using Coq as a library}

In previous versions, \texttt{coqmktop} was used to build custom
toplevels --- for example for better debugging or custom static
linking. Nowadays, the preferred method is to use \texttt{ocamlfind}.

The most basic custom toplevel is built using:
\begin{quotation}
\texttt{\% ocamlfind ocamlopt -thread -rectypes -linkall -linkpkg
  -package coq.toplevel toplevel/coqtop\_bin.ml -o my\_toplevel.native}
\end{quotation}

For example, to statically link LTAC, you can just do:
\begin{quotation}
\texttt{\% ocamlfind ocamlopt -thread -rectypes -linkall -linkpkg
  -package coq.toplevel -package coq.ltac toplevel/coqtop\_bin.ml -o my\_toplevel.native}
\end{quotation}
and similarly for other plugins.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section[Building a \Coq\ project with {\tt coq\_makefile}]
{Building a \Coq\ project with {\tt coq\_makefile}
\label{Makefile}
\ttindex{Makefile}
\ttindex{coq\_Makefile}
\ttindex{\_CoqProject}}

The majority of \Coq\ projects are very similar: a collection of {\tt .v}
files and eventually some {\tt .ml} ones (a \Coq\ plugin).  The main piece
of metadata needed in order to build the project are the command
line options to {\tt coqc} (e.g. {\tt -R, -I},
\SeeAlso Section~\ref{coqoptions}). Collecting the list of files and
options is the job of the {\tt \_CoqProject} file.

A simple example of a {\tt \_CoqProject} file follows:

\begin{verbatim}
-R theories/ MyCode
theories/foo.v
theories/bar.v
-I src/
src/baz.ml4
src/bazaux.ml
src/qux_plugin.mlpack
\end{verbatim}

Currently, both \CoqIDE{} and Proof General (version $\geq$ 4.3pre) understand
{\tt \_CoqProject} files and invoke \Coq\ with the desired options.

The {\tt coq\_makefile} utility can be used to set up a build infrastructure
for the \Coq\ project based on makefiles.  The recommended way of
invoking {\tt coq\_makefile} is the following one:

\begin{verbatim}
coq_makefile -f _CoqProject -o CoqMakefile
\end{verbatim}

Such command generates the following files:
\begin{description}
        \item[{\tt CoqMakefile}] is a generic makefile for GNU Make that provides targets to build the project (both {\tt .v} and {\tt .ml*} files), to install it system-wide in the {\tt coq-contrib} directory (i.e. where \Coq\ is installed) as well as to invoke {\tt coqdoc} to generate html documentation.

        \item[{\tt CoqMakefile.conf}] contains make variables assignments that reflect the contents of the {\tt \_CoqProject} file as well as the path relevant to \Coq{}.
\end{description}

An optional file {\bf {\tt CoqMakefile.local}} can be provided by the user in order to extend {\tt CoqMakefile}.  In particular one can declare custom actions to be performed before or after the build process. Similarly one can customize the install target or even provide new targets.  Extension points are documented in paragraph \ref{coqmakefile:local}.

The extensions of the files listed in {\tt \_CoqProject} is
used in order to decide how to build them.  In particular:

\begin{itemize}
\item {\Coq} files must use the \texttt{.v} extension
\item {\ocaml} files must use the \texttt{.ml} or \texttt{.mli} extension
\item {\ocaml} files that require pre processing for syntax extensions (like {\tt VERNAC EXTEND}) must use the \texttt{.ml4} extension
\item In order to generate a plugin one has to list all {\ocaml} modules (i.e. ``Baz'' for ``baz.ml'') in a \texttt{.mlpack} file (or \texttt{.mllib} file).
\end{itemize}

The use of \texttt{.mlpack} files has to be preferred over \texttt{.mllib}
files, since it results in a ``packed'' plugin: All auxiliary
modules (as {\tt Baz} and {\tt Bazaux}) are hidden inside
the plugin's ``name space'' ({\tt Qux\_plugin}).
This reduces the chances of begin unable to load two distinct plugins
because of a clash in their auxiliary module names.

\paragraph{CoqMakefile.local} %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\label{coqmakefile:local}

The optional file {\tt CoqMakefile.local} is included by the generated file
{\tt CoqMakefile}.  Such can contain two kinds of directives.

\begin{description}
  \item[Variable assignment] to the variables listed in the {\tt Parameters}
          section of the generated makefile.  Here we describe only few of them.
  \begin{description}
  \item[CAMLPKGS] can be used to specify third party findlib packages, and is
          passed to the OCaml compiler on building or linking of modules.
          Eg: {\tt -package yojson}.
  \item[CAMLFLAGS] can be used to specify additional flags to the OCaml
          compiler, like {\tt -bin-annot} or {\tt -w...}.
  \item[COQC, COQDEP, COQDOC] can be set in order to use alternative
          binaries (e.g. wrappers)
  \item[COQ\_SRC\_SUBDIRS] can be extended by including other paths in which {\tt *.cm*} files are searched. For example {\tt COQ\_SRC\_SUBDIRS+=user-contrib/Unicoq} lets you build a plugin containing OCaml code that depends on the OCaml code of {\tt Unicoq}.
  \end{description}
\item[Rule extension]
  The following makefile rules can be extended. For example
\begin{verbatim}
pre-all::
        echo "This line is print before making the all target"
install-extra::
        cp ThisExtraFile /there/it/goes
\end{verbatim}
  \begin{description}
  \item[pre-all::] run before the {\tt all} target.  One can use this
          to configure the project, or initialize sub modules or check
          dependencies are met.
  \item[post-all::] run after the {\tt all} target.  One can use this
          to run a test suite, or compile extracted code.
  \item[install-extra::] run after {\tt install}.  One can use this
          to install extra files.
  \item[install-doc::]  One can use this to install extra doc.
  \item[uninstall::]
  \item[uninstall-doc::]
  \item[clean::]
  \item[cleanall::]
  \item[archclean::]
  \item[merlin-hook::] One can append lines to the generated {\tt .merlin}
          file extending this target.
  \end{description}
\end{description}

\paragraph{Timing targets and performance testing} %%%%%%%%%%%%%%%%%%%%%%%%%%%
The generated \texttt{Makefile} supports the generation of two kinds
of timing data: per-file build-times, and per-line times for an
individual file.

The following targets and \texttt{Makefile} variables allow collection
of per-file timing data:
\begin{itemize}
\item \texttt{TIMED=1} --- passing this variable will cause
  \texttt{make} to emit a line describing the user-space build-time
  and peak memory usage for each file built.

  \texttt{Note}: On Mac OS, this works best if you've installed
  \texttt{gnu-time}.

  \texttt{Example}: For example, the output of \texttt{make TIMED=1}
  may look like this:
\begin{verbatim}
COQDEP Fast.v
COQDEP Slow.v
COQC Slow.v
Slow (user: 0.34 mem: 395448 ko)
COQC Fast.v
Fast (user: 0.01 mem: 45184 ko)
\end{verbatim}
\item \texttt{pretty-timed} --- this target stores the output of
  \texttt{make TIMED=1} into \texttt{time-of-build.log}, and displays
  a table of the times, sorted from slowest to fastest, which is also
  stored in \texttt{time-of-build-pretty.log}.  If you want to
  construct the log for targets other than the default one, you can
  pass them via the variable \texttt{TGTS}, e.g., \texttt{make
    pretty-timed TGTS="a.vo b.vo"}.

  \texttt{Note}: This target requires \texttt{python} to build the table.

  \texttt{Note}: This target will \emph{append} to the timing log; if
  you want a fresh start, you must remove the file
  \texttt{time-of-build.log} or run \texttt{make cleanall}.

  \texttt{Example}: For example, the output of \texttt{make
    pretty-timed} may look like this:
\begin{verbatim}
COQDEP Fast.v
COQDEP Slow.v
COQC Slow.v
Slow (user: 0.36 mem: 393912 ko)
COQC Fast.v
Fast (user: 0.05 mem: 45992 ko)
Time     | File Name
--------------------
0m00.41s | Total
--------------------
0m00.36s | Slow
0m00.05s | Fast
\end{verbatim}
\item \texttt{print-pretty-timed-diff} --- this target builds a table
  of timing changes between two compilations; run \texttt{make
    make-pretty-timed-before} to build the log of the ``before''
  times, and run \texttt{make make-pretty-timed-after} to build the
  log of the ``after'' times.  The table is printed on the command
  line, and stored in \texttt{time-of-build-both.log}.  This target is
  most useful for profiling the difference between two commits to a
  repo.

  \texttt{Note}: This target requires \texttt{python} to build the table.

  \texttt{Note}: The \texttt{make-pretty-timed-before} and
  \texttt{make-pretty-timed-after} targets will \emph{append} to the
  timing log; if you want a fresh start, you must remove the files
  \texttt{time-of-build-before.log} and
  \texttt{time-of-build-after.log} or run \texttt{make cleanall}
  \emph{before} building either the ``before'' or ``after'' targets.

  \texttt{Note}: The table will be sorted first by absolute time
  differences rounded towards zero to a whole-number of seconds, then
  by times in the ``after'' column, and finally lexicographically by
  file name.  This will put the biggest changes in either direction
  first, and will prefer sorting by build-time over subsecond changes
  in build time (which are frequently noise); lexicographic sorting
  forces an order on files which take effectively no time to compile.

  \texttt{Example}: For example, the output table from \texttt{make
    print-pretty-timed-diff} may look like this:
\begin{verbatim}
After    | File Name | Before   || Change    | % Change
--------------------------------------------------------
0m00.39s | Total     | 0m00.35s || +0m00.03s | +11.42%
--------------------------------------------------------
0m00.37s | Slow      | 0m00.01s || +0m00.36s | +3600.00%
0m00.02s | Fast      | 0m00.34s || -0m00.32s | -94.11%
\end{verbatim}
\end{itemize}

The following targets and \texttt{Makefile} variables allow collection
of per-line timing data:
\begin{itemize}
\item \texttt{TIMING=1} --- passing this variable will cause
  \texttt{make} to use \texttt{coqc -time} to write to a
  \texttt{.v.timing} file for each \texttt{.v} file compiled, which
  contains line-by-line timing information.

  \texttt{Example}: For example, running \texttt{make all TIMING=1} may
  result in a file like this:
\begin{verbatim}
Chars 0 - 26 [Require~Coq.ZArith.BinInt.] 0.157 secs (0.128u,0.028s)
Chars 27 - 68 [Declare~Reduction~comp~:=~vm_c...] 0. secs (0.u,0.s)
Chars 69 - 162 [Definition~foo0~:=~Eval~comp~i...] 0.153 secs (0.136u,0.019s)
Chars 163 - 208 [Definition~foo1~:=~Eval~comp~i...] 0.239 secs (0.236u,0.s)
\end{verbatim}

\item \texttt{print-pretty-single-time-diff
  BEFORE=path/to/file.v.before-timing
  AFTER=path/to/file.v.after-timing} --- this target will make a
  sorted table of the per-line timing differences between the timing
  logs in the \texttt{BEFORE} and \texttt{AFTER} files, display it,
  and save it to the file specified by the
  \texttt{TIME\_OF\_PRETTY\_BUILD\_FILE} variable, which defaults to
  \texttt{time-of-build-pretty.log}.

  To generate the \texttt{.v.before-timing} or
  \texttt{.v.after-timing} files, you should pass
  \texttt{TIMING=before} or \texttt{TIMING=after} rather than
  \texttt{TIMING=1}.

  \texttt{Note}: The sorting used here is the same as in the
  \texttt{print-pretty-timed-diff} target.

  \texttt{Note}: This target requires \texttt{python} to build the table.

  \texttt{Example}: For example, running
  \texttt{print-pretty-single-time-diff} might give a table like this:
\begin{verbatim}
After     | Code                                                | Before    || Change    | % Change
---------------------------------------------------------------------------------------------------
0m00.50s  | Total                                               | 0m04.17s  || -0m03.66s | -87.96%
---------------------------------------------------------------------------------------------------
0m00.145s | Chars 069 - 162 [Definition~foo0~:=~Eval~comp~i...] | 0m00.192s || -0m00.04s | -24.47%
0m00.126s | Chars 000 - 026 [Require~Coq.ZArith.BinInt.]        | 0m00.143s || -0m00.01s | -11.88%
   N/A    | Chars 027 - 068 [Declare~Reduction~comp~:=~nati...] | 0m00.s    || +0m00.00s | N/A
0m00.s    | Chars 027 - 068 [Declare~Reduction~comp~:=~vm_c...] |    N/A    || +0m00.00s | N/A
0m00.231s | Chars 163 - 208 [Definition~foo1~:=~Eval~comp~i...] | 0m03.836s || -0m03.60s | -93.97%
\end{verbatim}

\item \texttt{all.timing.diff}, \texttt{path/to/file.v.timing.diff}
  --- The \texttt{path/to/file.v.timing.diff} target will make a
  \texttt{.v.timing.diff} file for the corresponding \texttt{.v} file,
  with a table as would be generated by the
  \texttt{print-pretty-single-time-diff} target; it depends on having
  already made the corresponding \texttt{.v.before-timing} and
  \texttt{.v.after-timing} files, which can be made by passing
  \texttt{TIMING=before} and \texttt{TIMING=after}.  The
  \texttt{all.timing.diff} target will make such timing difference
  files for all of the \texttt{.v} files that the \texttt{Makefile}
  knows about.  It will fail if some \texttt{.v.before-timing} or
  \texttt{.v.after-timing} files don't exist.

  \texttt{Note}: This target requires \texttt{python} to build the table.
\end{itemize}

\paragraph{Reusing/extending the generated Makefile} %%%%%%%%%%%%%%%%%%%%%%%%%

Including the generated makefile with an {\tt include} directive is discouraged.
The contents of this file, including variable names
and status of rules shall change in the future.  Users are advised to
include {\tt Makefile.conf} or call a target of the generated Makefile
as in {\tt make -f Makefile target} from another Makefile.

One way to get access to all targets of the generated
\texttt{CoqMakefile} is to have a generic target for invoking unknown
targets.  For example:
\begin{verbatim}
# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
        $(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
        $(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
        @true
\end{verbatim}

\paragraph{Building a subset of the targets with -j} %%%%%%%%%%%%%%%%%%%%%%%%%

To build, say, two targets \texttt{foo.vo} and \texttt{bar.vo}
in parallel one can use \texttt{make only TGTS="foo.vo bar.vo" -j}.

Note that \texttt{make foo.vo bar.vo -j} has a different meaning for
the make utility, in particular it may build a shared prerequisite twice.

\paragraph{Notes for users of {\tt coq\_makefile} with version $<$ 8.7} %%%%%%

\begin{itemize}
\item Support for ``sub-directory'' is deprecated.  To perform actions before
        or after the build (like invoking make on a subdirectory) one can
        hook in {\tt pre-all} and {\tt post-all} extension points
\item \texttt{-extra-phony} and \texttt{-extra} are deprecated.  To provide
        additional target ({\tt .PHONY} or not) please use
        {\tt CoqMakefile.local}
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section[Modules dependencies]{Modules dependencies\label{Dependencies}\index{Dependencies}
  \ttindex{coqdep}}

In order to compute modules dependencies (so to use {\tt make}),
\Coq\ comes with an appropriate tool, {\tt coqdep}.

{\tt coqdep} computes inter-module dependencies for \Coq\ and
\ocaml\ programs, and prints the dependencies on the standard
output in a format readable by make.  When a directory is given as
argument, it is recursively looked at.

Dependencies of \Coq\ modules are computed by looking at {\tt Require}
commands ({\tt Require}, {\tt Requi\-re Export}, {\tt Require Import},
but also at the command {\tt Declare ML Module}.

Dependencies of \ocaml\ modules are computed by looking at
\verb!open! commands and the dot notation {\em module.value}. However,
this is done approximately and you are advised to use {\tt ocamldep}
instead for the \ocaml\ modules dependencies.

See the man page of {\tt coqdep} for more details and options.

The build infrastructure generated by {\tt coq\_makefile}
uses {\tt coqdep} to automatically compute the dependencies
among the files part of the project.

\section[Documenting \Coq\ files with coqdoc]{Documenting \Coq\ files with coqdoc\label{coqdoc}
\ttindex{coqdoc}}

\input{./coqdoc}

\section[Embedded \Coq\ phrases inside \LaTeX\ documents]{Embedded \Coq\ phrases inside \LaTeX\ documents\label{Latex}
  \ttindex{coq-tex}\index{Latex@{\LaTeX}}}

When writing a documentation about a proof development, one may want
to insert \Coq\ phrases inside a \LaTeX\ document, possibly together with
the corresponding answers of the system. We provide a
mechanical way to process such \Coq\ phrases embedded in \LaTeX\ files: the
{\tt coq-tex} filter.  This filter extracts Coq phrases embedded in
LaTeX files, evaluates them, and insert the outcome of the evaluation
after each phrase.

Starting with a file {\em file}{\tt.tex} containing \Coq\ phrases,
the {\tt coq-tex} filter produces a file named {\em file}{\tt.v.tex} with
the \Coq\ outcome.

There are options to produce the \Coq\ parts in smaller font, italic,
between horizontal rules, etc.
See the man page of {\tt coq-tex} for more details.

\medskip\noindent {\bf Remark.} This Reference Manual and the Tutorial
have been completely produced with {\tt coq-tex}.


\section[\Coq\ and \emacs]{\Coq\ and \emacs\label{Emacs}\index{Emacs}}

\subsection{The \Coq\ Emacs mode}

\Coq\ comes with a Major mode for \emacs, {\tt gallina.el}. This mode provides
syntax highlighting
and also a rudimentary indentation facility
in the style of the Caml \emacs\ mode.

Add the following lines to your \verb!.emacs! file:

\begin{verbatim}
  (setq auto-mode-alist (cons '("\\.v$" . coq-mode) auto-mode-alist))
  (autoload 'coq-mode "gallina" "Major mode for editing Coq vernacular." t)
\end{verbatim}

The \Coq\ major mode is triggered by visiting a file with extension {\tt .v},
or manually with the command \verb!M-x coq-mode!.
It gives you the correct syntax table for
the \Coq\ language, and also a rudimentary indentation facility:
\begin{itemize}
  \item pressing {\sc Tab} at the beginning of a line indents the line like
    the line above;

  \item extra {\sc Tab}s increase the indentation level
    (by 2 spaces by default);

  \item M-{\sc Tab} decreases the indentation level.
\end{itemize}

An inferior mode to run \Coq\ under Emacs, by Marco Maggesi, is also
included in the distribution, in file \texttt{inferior-coq.el}.
Instructions to use it are contained in this file.

\subsection[{\ProofGeneral}]{{\ProofGeneral}\index{Proof General@{\ProofGeneral}}}

{\ProofGeneral} is a generic interface for proof assistants based on
Emacs. The main idea is that the \Coq\ commands you are
editing are sent to a \Coq\ toplevel running behind Emacs and the
answers of the system automatically inserted into other Emacs buffers.
Thus you don't need to copy-paste the \Coq\ material from your files
to the \Coq\ toplevel or conversely from the \Coq\ toplevel to some
files.

{\ProofGeneral} is developed and distributed independently of the
system \Coq. It is freely available at \verb!https://proofgeneral.github.io/!.


\section[Module specification]{Module specification\label{gallina}\ttindex{gallina}}

Given a \Coq\ vernacular file, the {\tt gallina} filter extracts its
specification (inductive types declarations, definitions, type of
lemmas and theorems), removing the proofs parts of the file. The \Coq\
file {\em file}{\tt.v} gives birth to the specification file
{\em file}{\tt.g} (where the suffix {\tt.g} stands for \gallina).

See the man page of {\tt gallina} for more details and options.


\section[Man pages]{Man pages\label{ManPages}\index{Man pages}}

There are man pages for the commands {\tt coqdep}, {\tt gallina} and
{\tt coq-tex}. Man pages are installed at installation time
(see installation instructions in file {\tt INSTALL}, step 6).

%BEGIN LATEX
\RefManCutCommand{ENDREFMAN=\thepage}
%END LATEX

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
