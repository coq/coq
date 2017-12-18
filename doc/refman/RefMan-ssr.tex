\achapter{The SSReflect proof language}
%HEVEA\cutname{ssreflect.html}
\aauthor{Georges Gonthier, Assia Mahboubi, Enrico Tassi}

\newcommand{\ssr}{{\sc SSReflect}}

% listing
\ifhevea\newcommand{\ssrC}[1]{\texttt{#1}}\else\newcommand{\ssrC}[1]{\text{\lstinline!#1!}}\fi
\ifhevea\renewenvironment{center}{\@open{div}{class="center"}\@open{div}{class="centered"}}{\@close{div}\@close{div}}\fi
% non-terminal
%\newcommand\ssrN[2][]{\ensuremath{\langle\mbox{\itshape\rmfamily\small #2}\rangle_{#1}}}
\newcommand\ssrN[2][]{{\textsl {#2}}\ensuremath{_{#1}}}
\ifhevea\newcommand{\underbar}[1]{\underline{#1}}\fi

% TODO: only use \ssrC
\let\ssrL=\lstinline

\newcommand{\iitem}{{\it i-item}}
\newcommand{\ditem}{{\it d-item}}
\newcommand{\optional}[1]{{\it[}#1{\it]}}
\newcommand{\optsep}{{\it|}}
\newcommand{\idx}[1]{\tacindex{#1 (ssreflect)}}
\newcommand{\idxC}[1]{\comindex{#1 (ssreflect)}}

\newenvironment{new}%
  {\begin{Sbox}\begin{minipage}{0.97\textwidth}%
    \begin{flushright}\textcolor{red}{\fbox{Version 1.3}}%
      \end{flushright}\noindent}%
  {\end{minipage}\end{Sbox}\noindent\doublebox{\TheSbox}}
\section{Introduction}\label{sec:intro}

This chapter describes a set of tactics known as \ssr{}
originally designed to provide support for the so-called \emph{small scale
reflection} proof methodology.  Despite the original purpose this set of tactic
is of general interest and is available in Coq starting from version 8.7.

\ssr{} was developed independently of the tactics described in
Chapter~\ref{Tactics}.  Indeed the scope of the tactics part of
\ssr{} largely overlaps with the standard set of tactics.  Eventually
the overlap will be reduced in future releases of Coq.

Proofs written in \ssr{} typically look quite different from the
ones written using only tactics as per Chapter~\ref{Tactics}.
We try to summarise here the most ``visible'' ones in order to
help the reader already accustomed to the tactics described in
Chapter~\ref{Tactics} to read this chapter.

The first difference between the tactics described in this
chapter and the tactics described in Chapter~\ref{Tactics} is the way
hypotheses are managed (we call this \emph{bookkeeping}).
In Chapter~\ref{Tactics} the most common
approach is to avoid moving explicitly hypotheses back and forth
between the context and the conclusion of the goal. On the contrary
in \ssr{}
all bookkeeping is performed on the conclusion of the goal, using for
that purpose a couple of syntactic constructions behaving similar to
tacticals (and often named as such in this chapter).
The \ssrC{:} tactical  moves hypotheses from the context to the
conclusion, while \ssrC{=>} moves hypotheses from the
conclusion to the context, and \ssrC{in} moves back
and forth an hypothesis from the context to the conclusion for the
time of applying an action to it.

While naming hypotheses is commonly done by means of an \ssrC{as}
clause in the basic model of Chapter~\ref{Tactics}, it is here to
\ssrC{=>} that this task is devoted. As tactics leave
new assumptions in the conclusion, and are often followed by
\ssrC{=>} to explicitly name them.
While generalizing the goal is normally
not explicitly needed in Chapter~\ref{Tactics}, it is an explicit
operation performed by \ssrC{:}.

Beside the difference of bookkeeping model, this chapter includes
specific tactics which have no explicit counterpart in
Chapter~\ref{Tactics} such as tactics to mix forward steps and
generalizations as \ssrC{generally have} or \ssrC{without loss}.

\ssr{} adopts the point of view that rewriting, definition
expansion and partial evaluation participate all to a same concept of
rewriting a goal in a larger sense. As such, all these functionalities are
provided by the \ssrC{rewrite} tactic.

\ssr{} includes a little language of patterns to select subterms in tactics
or tacticals where it matters.  Its most notable application
is in the \ssrC{rewrite} tactic, where patterns are used to specify
where the rewriting step has to take place.

Finally, \ssr{} supports so-called reflection steps, typically
allowing to switch back and forth between the computational view and
logical view of a concept.

To conclude it is worth mentioning that \ssr{} tactics
can be mixed with non \ssr{} tactics in the same proof,
or in the same Ltac expression.  The few exceptions
to this statement are described in section~\ref{sec:compat}.

\iffalse
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{How to read this documentation}

The syntax of the tactics is presented as follows:
\begin{itemize}
\item \ssrC{terminals} are in typewriter font and \ssrN{non terminals} are
  between angle brackets.
\item Optional parts of the grammar are surrounded by \optional{ }
  brackets. These should not be confused with verbatim brackets
  \ssrC{[ ]}, which are delimiters in the \ssr{} syntax.
\item A vertical rule {\optsep} indicates an alternative in the syntax, and
  should not be confused with a
  verbatim vertical rule between verbatim brackets \ssrC{[ | ]}.
\item A non empty list of non terminals (at least one item should be
  present) is represented by \ssrN{non terminals}$^+$. A possibly empty
  one is represented by \ssrN{non terminals}$^*$.
\item In a non empty list of non terminals, items are separated by blanks.
\end{itemize}
\fi

% Hevea has no colors
\ifhevea \else
\noindent We follow the default color scheme of the \ssr{} mode for
ProofGeneral provided in the distribution:

\centerline{
\textcolor{dkblue}{\texttt{tactic}} or \textcolor{dkviolet}{\tt
  Command} or \textcolor{dkgreen}{\tt keyword} or
\textcolor{dkpink}{\tt tactical}}

\noindent Closing tactics/tacticals like \ssrC{exact} or \ssrC{by} (see section
\ref{ssec:termin}) are in red.
\fi

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{Acknowledgments}
The authors would like to thank Frédéric Blanqui, François Pottier
and Laurence Rideau for their comments and suggestions.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newpage\section{Usage}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Getting started}\label{sec:files}
To be available, the tactics presented in this manual need the
following minimal set of libraries to loaded: {\tt ssreflect.v}, {\tt
ssrfun.v} and {\tt ssrbool.v}. Moreover, these tactics come with a
methodology specific to the authors of Ssreflect and which requires a
few options to be set in a different way than in their default
way. All in all, this corresponds to working in the following context:

\begin{lstlisting}
  From Coq Require Import ssreflect ssrfun ssrbool.
  Set Implicit Arguments.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Compatibility issues}\label{sec:compat}
Requiring the above modules creates an environment which
is mostly compatible with the rest of \Coq{}, up to a few discrepancies:
\begin{itemize}
\item New keywords (\ssrC{is}) might clash with variable, constant,
tactic or tactical names, or with quasi-keywords in tactic or
vernacular notations.
\item New tactic(al)s names (\ssrC{last}, \ssrC{done}, \ssrC{have},
  \ssrC{suffices}, \ssrC{suff},
  \ssrC{without loss}, \ssrC{wlog}, \ssrC{congr}, \ssrC{unlock}) might clash
  with user tactic names.
\item Identifiers with both leading and trailing \ssrC{_}, such as \ssrC{_x_},
are reserved by \ssr{} and cannot appear in scripts.
\item The extensions to the \ssrC{rewrite} tactic are partly
incompatible with those available in current versions of \Coq{};
in particular:
\ssrC{rewrite .. in (type of k)} or \\ \ssrC{rewrite .. in *} or any other
variant of \ssrC{rewrite} will not work, and the \ssr{} syntax and semantics for occurrence selection and
rule chaining is different.

Use an explicit rewrite direction (\ssrC{rewrite <-} $\dots$ or \ssrC{rewrite ->} $\dots$)
to access the \Coq{} \ssrC{rewrite} tactic.
\item New symbols (\ssrC{//, /=, //=}) might clash with adjacent existing
  symbols (e.g., '\ssrC{//}') instead of '\ssrC{/}''\ssrC{/}'). This can be avoided
  by inserting white spaces.
\item New constant and theorem names might clash with the user
theory. This can be avoided by not importing all of \ssr{}:
\begin{lstlisting}
  From Coq Require ssreflect.
  Import ssreflect.SsrSyntax.
\end{lstlisting}
Note that the full syntax of \ssr{}'s {\tt rewrite} and reserved identifiers are
enabled only if the \ssrC{ssreflect} module has been required and if
\ssrC{SsrSyntax} has been imported. Thus a file that requires (without importing)
 \ssrC{ssreflect} and imports \ssrC{SsrSyntax}, can be
required and imported without automatically enabling \ssr{}'s
extended rewrite syntax and reserved identifiers.
\item Some user notations (in particular, defining an infix ';') might
interfere with the "open term", parenthesis free, syntax of tactics
such as \ssrC{have}, \ssrC{set} and \ssrC{pose}.
\item The generalization of \ssrC{if} statements to non-Boolean
conditions is turned off by \ssr{}, because it is mostly subsumed by
\ssrC{Coercion} to \ssrC{bool} of the \ssrC{sum}XXX types (declared in
\ssrC{ssrfun.v})
and the \ssrC{if} {\term} \ssrC{is} \ssrN{pattern} \ssrC{then} {\term} \ssrC{else} {\term} construct (see
\ref{ssec:patcond}). To use the generalized form, turn off the \ssr{}
Boolean \ssrC{if} notation using the command:
\begin{lstlisting}
  Close Scope boolean_if_scope.
\end{lstlisting}
\item The following two options can be unset to disable the
      incompatible \ssrC{rewrite} syntax and allow
      reserved identifiers to appear in scripts.
\begin{lstlisting}
  Unset SsrRewrite.
  Unset SsrIdents.
\end{lstlisting}
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Gallina extensions}

Small-scale reflection makes an extensive use of the programming
subset of Gallina, \Coq{}'s logical specification language. This subset
is quite suited to the description of functions on representations,
because it closely follows the well-established design of the ML
programming language. The \ssr{} extension provides three additions
to Gallina, for pattern assignment, pattern testing, and polymorphism;
these mitigate minor but annoying discrepancies between Gallina and ML.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Pattern assignment}\label{ssec:patass}
The \ssr{} extension provides the following construct for
irrefutable pattern matching, that is, destructuring assignment:

\ssrC{let: } \ssrN{pattern}  \ssrC{:=} \ssrN[1]{term} \ssrC{in} \ssrN[2]{term}

Note the colon `\ssrC{:}' after the \ssrC{let} keyword, which avoids any
ambiguity with a function
definition or \Coq{}'s basic destructuring \ssrC{let}. The \ssrC{let:}
construct differs from the latter in that
\begin{itemize}
\item The pattern can be nested (deep pattern matching), in
  particular, this allows expression of the form:
\begin{lstlisting}
 let: exist (x, y) p_xy := Hp in ...
\end{lstlisting}
\item The destructured constructor is explicitly given in the
  pattern, and is used for type inference, e.g.,
\begin{lstlisting}
  Let f u := let: (m, n) := u in m + n.
\end{lstlisting}
using a colon \ssrC{let:}, infers \ssrC{f : nat * nat -> nat}, whereas
\begin{lstlisting}
  Let f u := let (m, n) := u in m + n.
\end{lstlisting}
with a usual \ssrC{let}, requires an extra type annotation.
\end{itemize}
The \ssrC{let:} construct is just (more legible) notation for the primitive Gallina expression

\begin{center}
\ssrC{match} \ssrN[1]{term} \ssrC{with} \ssrN{pattern} \ssrC{=>} \ssrN[2]{term} \ssrC{end}
\end{center}

The \ssr{} destructuring assignment supports all the dependent match
annotations; the  full syntax is

\begin{center}
\ssrC{let:} \ssrN[1]{pattern} \ssrC{as} \ssrN{ident} \ssrC{in} \ssrN[2]{pattern} \ssrC{:=} \ssrN[1]{term} \ssrC{return} \ssrN[2]{term} \ssrC{in} \ssrN[3]{term}
\end{center}

where \ssrN[2]{pattern} is a \emph{type} pattern and \ssrN[1]{term} and
\ssrN[2]{term} are types.

When the \ssrC{as} and \ssrC{return} are both present, then \ssrN{ident} is bound
in both the type \ssrN[2]{term} and the expression \ssrN[3]{term};
variables in the optional type pattern \ssrN[2]{pattern} are
bound only in the type \ssrN[2]{term}, and other variables in \ssrN[1]{pattern} are
bound only in the expression \ssrN[3]{term}, however.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Pattern conditional}\label{ssec:patcond}
The following construct can be used for a refutable pattern matching,
that is, pattern testing:

\begin{center}
\ssrC{if}\ \ssrN[1]{term} \ssrC{is} \ssrN[1]{pattern} \ssrC{then} \ssrN[2]{term} \ssrC{else} \ssrN[3]{term}
\end{center}

Although this construct is not strictly ML (it does exits in variants
such as the pattern calculus or the $\rho$-calculus), it turns out to be
very convenient for writing functions on representations,
because most such functions manipulate simple datatypes such as Peano
integers, options,
lists, or binary trees, and the pattern conditional above is almost
always the right construct
for analyzing such simple types. For example, the \ssrC{null} and
\ssrC{all} list function(al)s can be defined as follows:
\begin{lstlisting}
  Variable d: Set.
  Fixpoint |*null*| (s : list d) := if s is nil then true else false.
  Variable a : d -> bool.
  Fixpoint |*all*| (s : list d) : bool :=
     if s is cons x s' then a x && all s' else true.
\end{lstlisting}

The pattern conditional also provides a notation for destructuring
assignment with a refutable pattern, adapted to the pure functional
setting of Gallina, which lacks a \\\texttt{Match\_Failure} exception.

Like \ssrC{let:} above, the \ssrC{if}$\dots$\ssrC{is} construct is just (more legible)
notation for the primitive Gallina expression:

\begin{center}
\ssrC{match} \ssrN[1]{term} \ssrC{with} \ssrN{pattern} \ssrC{=>} \ssrN[2]{term} \ssrC{| _ =>} \ssrN[2]{term} \ssrC{end}
\end{center}

Similarly, it will always be displayed as the expansion of this form
in terms of primitive \ssrC{match} expressions (where the default
expression $\ssrN[3]{term}$ may be replicated).


Explicit pattern testing also largely subsumes the generalization of
the \ssrC{if} construct to all binary datatypes; compare:

\begin{center}
\ssrC{if} {\term} \ssrC{is inl _ then} \ssrN[l]{term} \ssrC{else} \ssrN[r]{term}
\end{center}

and:

\begin{center}
\ssrC{if} {\term} \ssrC{then} \ssrN[l]{term} \ssrC{else} \ssrN[r]{term}
\end{center}

The latter appears to be marginally shorter, but it is quite
ambiguous, and indeed often
requires an explicit annotation term : \ssrC{\{_\}+\{_\}} to type-check,
which evens the character count.

Therefore, \ssr{} restricts by default the condition of a plain \ssrC{if}
construct to the standard \ssrC{bool} type; this avoids spurious type
annotations, e.g., in:
\begin{lstlisting}
  Definition |*orb*| b1 b2 := if b1 then true else b2.
\end{lstlisting}
As pointed out in section~\ref{sec:compat}, this restriction can be removed with
the command:
\begin{lstlisting}
  Close Scope boolean_if_scope.
\end{lstlisting}
Like \ssrC{let:} above, the \ssrC{if} {\term} \ssrC{is} \ssrN{pattern}
\ssrC{else} {\term} construct
supports the dependent \ssrC{match} annotations:

\begin{center}
\ssrC{if} \ssrN[1]{term} \ssrC{is} \ssrN[1]{pattern} \ssrC{as} \ssrN{ident} \ssrC{in} \ssrN[2]{pattern} \ssrC{return} \ssrN[2]{term} \ssrC{then} \ssrN[3]{term} \ssrC{else} \ssrN[4]{term}
\end{center}

As in \ssrC{let:} the variable \ssrN{ident} (and those in
the type pattern \ssrN[2]{pattern}) are bound in \ssrN[2]{term}; \ssrN{ident} is
also bound in \ssrN[3]{term} (but not in \ssrN[4]{term}), while the
variables in \ssrN[1]{pattern} are bound only in \ssrN[3]{term}.

\noindent
Another variant allows to treat the else case first:

\begin{center}
\ssrC{if} \ssrN[1]{term} \ssrC{isn't} \ssrN[1]{pattern} \ssrC{then} \ssrN[2]{term} \ssrC{else} \ssrN[3]{term}
\end{center}

Note that \ssrN[1]{pattern} eventually binds variables in \ssrN[3]{term}
and not \ssrN[2]{term}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Parametric polymorphism}\label{ssec:parampoly}

Unlike ML, polymorphism in core Gallina is explicit: the type
parameters of polymorphic  functions must be declared explicitly, and
supplied at each point of use. However, \Coq{} provides two features
to suppress redundant parameters:
\begin{itemize}
\item Sections are used to provide (possibly implicit) parameters for
  a set of definitions.
\item Implicit arguments declarations are used to tell \Coq{} to use
  type inference to deduce some parameters from the context at each
  point of call.
\end{itemize}
The combination of these features provides a fairly good emulation of ML-style
polymorphism, but unfortunately this emulation breaks down for
higher-order programming. Implicit arguments are indeed not inferred
at all points of use, but only at
points of call, leading to  expressions such as
\begin{lstlisting}
  Definition |*all_null*| (s : list T) := all (@null T) s.
\end{lstlisting}
Unfortunately, such higher-order expressions are quite frequent in
representation functions, especially those which use \Coq{}'s
\ssrC{Structure}s to emulate Haskell type classes.

Therefore, \ssr{} provides a variant of \Coq{}'s implicit argument
declaration, which  causes \Coq{} to fill in some implicit parameters
at each point of use, e.g., the above definition can be written:
\begin{lstlisting}
  Definition |*all_null*| (s : list d) := all null s.
\end{lstlisting}
Better yet, it can be omitted entirely, since \ssrC{all_null s} isn't
much of an improvement over \ssrC{all null s}.

The syntax of the new declaration is

\begin{center}
\ssrC{Prenex Implicits} \ssrN{ident}$^+$.
\end{center}

Let us denote $_1 \dots c_n$ the list of identifiers given to a
\ssrC{Prenex Implicits} command.
The command checks that each $c_i$ is the name of a functional
constant, whose implicit arguments are prenex, i.e., the first $n_i >
0$ arguments of $c_i$ are implicit; then it assigns
\ssrC{Maximal Implicit} status to these arguments.

As these prenex implicit arguments are ubiquitous and have often large
display strings, it is strongly recommended to change the default
display settings of \Coq{} so that they are not printed (except after a
\ssrC{Set Printing All} command).
All \ssr{} library files thus start with the incantation
\begin{lstlisting}
  Set Implicit Arguments.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Anonymous arguments}

When in a definition, the type of a certain argument is mandatory, but
not its name, one usually use ``arrow'' abstractions for prenex
arguments, or the \ssrC{(_ : }{\term}\ssrC{)} syntax for inner arguments.
In \ssr{}, the latter can be replaced by the open syntax `\ssrC{of\ }{\term}'
or (equivalently)  `\ssrC{& }{\term}', which are both syntactically
equivalent to a \ssrC{(_ : }{\term}\ssrC{)} expression.

For instance, the usual two-contrsuctor polymorphic type \ssrC{list},
i.e. the one of the
standard {\tt List} library, can be defined by the following
declaration:
\begin{lstlisting}
  Inductive list (A : Type) : Type := nil | cons of A & list A.
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Wildcards}\label{ssec:wild}

The terms passed as arguments
to \ssr{} tactics can contain \emph{holes}, materialized by wildcards
\ssrC{_}.
Since \ssr{} allows a more powerful form of type inference for these
arguments, it enhances the possibilities of using such wildcards.
These holes are in particular used as a convenient shorthand for
abstractions, especially in local definitions or type expressions.

Wildcards may be interpreted as abstractions (see for example sections
\ref{ssec:pose} and \ref{ssec:struct}), or their content can be
inferred from the whole
context of the goal (see for example section \ref{ssec:set}).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Definitions}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Definitions}\label{ssec:pose}
\idx{pose \dots{} := \dots{}}
\idx{pose fix \dots{} := \dots{}}
\idx{pose cofix \dots{} := \dots{}}

The \ssrC{pose} tactic allows to add a defined constant to a
proof context. \ssr{} generalizes this tactic in several ways.
In particular, the \ssr{} \ssrC{pose} tactic supports \emph{open syntax}:
the body of
the definition does not need surrounding parentheses. For instance:
\begin{lstlisting}
  pose t := x + y.
\end{lstlisting}
is a valid tactic expression.

The \ssrC{pose} tactic is also improved for the
local definition of higher order terms.
Local definitions of functions can use the same syntax as
global ones. The tactic:
\begin{lstlisting}
  pose f x y := x + y.
\end{lstlisting}
adds to the context the defined constant:
\begin{lstlisting}
  f := fun x y : nat => x + y : nat -> nat -> nat
\end{lstlisting}

The \ssr{} \ssrC{pose} tactic also supports (co)fixpoints,
by providing the local counterpart of the
\ssrC{Fixpoint f := $\dots$ } and \ssrC{CoFixpoint f := $\dots$ } constructs.
For instance, the following tactic:
\begin{lstlisting}
  pose fix f (x y : nat) {struct x} : nat :=
      if x is S p then S (f p y) else 0.
\end{lstlisting}
defines a local fixpoint \ssrC{f}, which mimics the standard \ssrC{plus}
operation on natural numbers.

Similarly, local cofixpoints can be defined by a tactic of the form:
\begin{lstlisting}
  pose cofix f (arg : T) ...
\end{lstlisting}

The possibility to include wildcards in the body of the definitions
 offers a smooth
way of defining local abstractions. The type of ``holes'' is
guessed by type inference, and the holes are abstracted.
For instance the tactic:
\begin{lstlisting}
  pose f := _ + 1.
\end{lstlisting}
is shorthand for:
\begin{lstlisting}
  pose f n := n + 1.
\end{lstlisting}

When the local definition of a function involves both arguments and
holes, hole abstractions appear first. For instance, the
tactic:
\begin{lstlisting}
  pose f x := x + _.
\end{lstlisting}
is shorthand for:
\begin{lstlisting}
  pose f n x := x + n.
\end{lstlisting}


The interaction of the \ssrC{pose} tactic with the interpretation of
implicit arguments results in a powerful and concise syntax for local
definitions involving dependent types.
For instance, the tactic:
\begin{lstlisting}
  pose f x y := (x, y).
\end{lstlisting}
adds to the context the local definition:
\begin{lstlisting}
  pose f (Tx Ty : Type) (x : Tx) (y : Ty) := (x, y).
\end{lstlisting}
The generalization of wildcards makes the use of the \ssrC{pose} tactic
resemble ML-like definitions of polymorphic functions.

% The use of \ssrC{Prenex Implicits} declarations (see section
% \ref{ssec:parampoly}), makes this feature specially convenient.
% Note that this combines with the interpretation of wildcards, and that
% it is possible to define:
% \begin{lstlisting}
%   pose g x y : prod _ nat := (x, y).
% \end{lstlisting}
% which is equivalent to:
% \begin{lstlisting}
%   pose g x (y : nat) := (x, y).
% \end{lstlisting}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Abbreviations}\label{ssec:set}
\idx{set \dots{} := \dots{}}


The \ssr{} \ssrC{set} tactic performs abbreviations: it introduces a
defined constant for a subterm appearing in the goal and/or in the
context.

\ssr{} extends the \ssrC{set} tactic by supplying:
\begin{itemize}
\item an open syntax, similarly to the \ssrC{pose} tactic;
\item a more aggressive matching algorithm;
\item an improved interpretation of wildcards, taking advantage of the
  matching algorithm;
\item an improved occurrence selection mechanism allowing to abstract only
  selected occurrences of a term.
\end{itemize}

The general syntax of this tactic is
\begin{center}
\ssrC{set} \ssrN{ident} \optional{\ssrC{:} \ssrN[1]{term}} \ssrC{:=} \optional{\ssrN{occ-switch}} \ssrN[2]{term}
\end{center}
\begin{center}
\ssrN{occ-switch} ::= \ssrC{\{}[\ssrC{+}|\ssrC{-}] {\naturalnumber}$^*$ \ssrC{\}}
\end{center}


where:

\begin{itemize}
\item \ssrN{ident} is a fresh identifier chosen by the user.
\item \ssrN[1]{term} is
an optional type annotation. The type annotation \ssrN[1]{term} can be
given in open syntax (no surrounding parentheses). If no \ssrN{occ-switch}
(described hereafter) is present, it is also
the case for \ssrN[2]{term}.
On the other hand, in  presence of \ssrN{occ-switch}, parentheses
surrounding \ssrN[2]{term} are mandatory.
\item In the occurrence switch \ssrN{occ-switch}, if the first element
  of the list is a {\naturalnumber}, this element should be a number, and not
  an Ltac variable. The empty list \ssrC{\{\}} is not interpreted as a
  valid occurrence switch.
\end{itemize}
% For example, the script:
% \begin{lstlisting}
%   Goal forall (f : nat -> nat)(x y : nat), f x + f x = f x.
%   move=> f x y.
% \end{lstlisting}

The tactic:
\begin{lstlisting}
  set t := f _.
\end{lstlisting}
transforms the goal  \ssrC{f x + f x = f x} into \ssrC{t + t = t}, adding
\ssrC{t := f x} to the context, and the tactic:
\begin{lstlisting}
  set t := {2}(f _).
\end{lstlisting}
transforms it into \ssrC{f x + t = f x}, adding \ssrC{t := f x} to the context.

The type annotation \ssrN[1]{term} may
contain wildcards, which will be filled with the appropriate value by
the matching process.

The tactic first tries to find a subterm of the goal matching
\ssrN[2]{term} (and its type \ssrN[1]{term}),
and stops at the first subterm it finds. Then the occurrences
of this subterm selected by the optional \ssrN{occ-switch} are replaced
by \ssrN{ident} and a definition \ssrN{ident} \ssrC{:=} {\term} is added to
the context. If no \ssrN{occ-switch} is present, then all the
occurrences are abstracted.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Matching}

The matching algorithm compares a pattern \textit{term}
 with a subterm of the goal by comparing their heads
and then pairwise unifying their arguments (modulo conversion). Head
symbols match under the following conditions:

\begin{itemize}
\item If the head of \textit{term} is a constant, then it
  should be syntactically equal to the head symbol of the subterm.
\item If this head is a projection of a canonical structure,
  then canonical structure equations are used for the matching.
\item If the head of \textit{term} is \emph{not} a constant, the
  subterm should have the same structure ($\lambda$ abstraction,
  \ssrC{let}$\dots$\ssrC{in} structure \dots).
\item If the head of \textit{term} is a hole, the subterm should have
  at least as many arguments as  \textit{term}. For instance the tactic:
\begin{lstlisting}
  set t := _ x.
\end{lstlisting}
transforms the goal \ssrL-x + y = z- into \ssrC{t y = z} and adds
\ssrC{t := plus x : nat -> nat} to the context.

\item In the special case where \textit{term} is of the form
  \ssrC{(let f := }$t_0$ \ssrC{in f) }$t_1\dots t_n$,
 then the pattern \textit{term} is treated
as \ssrC{(_ }$t_1\dots t_n$\ssrC{)}. For each subterm in
the goal having the form $(A\  u_1\dots u_{n'})$ with $n' \geq n$, the
matching algorithm successively tries to find the largest
partial application $(A\ u_1\dots u_{i'})$ convertible to the head
$t_0$ of \textit{term}. For instance the following tactic:
\begin{lstlisting}
  set t := (let g y z := y.+1 + z in g) 2.
\end{lstlisting}
transforms the goal
\begin{lstlisting}
  (let f x y z := x + y + z in f 1) 2 3 = 6.
\end{lstlisting}
into \ssrC{t 3 = 6} and adds the local definition of \ssrC{t} to the
context.
\end{itemize}

Moreover:
\begin{itemize}
\item Multiple holes in \textit{term} are treated as independent
  placeholders. For instance, the tactic:
\begin{lstlisting}
  set t := _ + _.
\end{lstlisting}
transforms the goal \ssrC{x + y = z} into \ssrC{t = z} and pushes
\ssrC{t := x + y : nat} in the context.
\item The type of the subterm matched should fit the type
  (possibly casted by some type annotations) of the pattern
  \textit{term}.
\item The replacement of the subterm found by the instantiated pattern
  should not capture variables, hence the following script:
\begin{lstlisting}
  Goal forall x : nat, x + 1 = 0.
  set u := _ + 1.
\end{lstlisting}
raises an error message, since \ssrC{x} is bound in the goal.
\item Typeclass inference should fill in any residual hole, but
matching should never assign a value to a global existential variable.

\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Occurrence selection}\label{sssec:occselect}

\ssr{} provides a generic syntax for the selection of occurrences by
their position indexes. These \emph{occurrence switches} are shared by
all
\ssr{} tactics which require control on subterm selection like rewriting,
generalization, \dots

An \emph{occurrence switch} can be:
\begin{itemize}
\item A list \ssrC{\{} {\naturalnumber}$^*$ \ssrC{\}} of occurrences affected by the
  tactic.
For instance, the tactic:
\begin{lstlisting}
  set x := {1 3}(f 2).
\end{lstlisting}
transforms the goal \ssrC{f 2 + f 8 = f 2 + f 2} into
\ssrC{x + f 8 = f 2  + x}, and adds the abbreviation
\ssrC{x := f 2} in the
context. Notice that some occurrences of a
given term may be hidden to the user, for example because of a
notation. The vernacular \ssrC{$\texttt{\textcolor{dkviolet}{Set }}$
  Printing All} command displays all
these hidden occurrences and should be used to find the correct
coding of the occurrences to be selected\footnote{Unfortunately,
even after a call to the Set Printing All command, some occurrences are
still not displayed to the user, essentially the ones possibly hidden
in the predicate of a dependent match structure.}. For instance, the
following script:
\begin{lstlisting}
  Notation "a < b":= (le (S a) b).
  Goal forall x y, x < y -> S x < S y.
  intros x y; set t := S x.
\end{lstlisting}
generates the goal
\ssrC{t <= y -> t < S y} since \ssrC{x < y} is now a notation for
\ssrC{S x <= y}.
\item A list \ssrC{\{}{\naturalnumber}$^+$\ssrC{\}}. This is equivalent to
  \ssrC{\{} {\naturalnumber}$^+$ \ssrC{\}} but the list should start with a number, and
  not with an Ltac variable.
\item A list \ssrC{\{}{\naturalnumber}$^*$\ssrC{\}} of occurrences \emph{not} to be
  affected by the tactic. For instance, the tactic:
\begin{lstlisting}
  set x := {-2}(f 2).
\end{lstlisting}
behaves like
\begin{lstlisting}
  set x := {1 3}(f 2).
\end{lstlisting}
on the goal \ssrL-f 2 + f 8 = f 2 + f 2- which has three occurrences of
the the term \ssrC{f 2}
\item In particular, the switch \ssrC{\{+\}} selects \emph{all} the
  occurrences. This switch is useful to turn
  off the default behavior of a tactic which automatically clears
  some assumptions (see section \ref{ssec:discharge} for instance).
\item The switch \ssrC{\{-\}} imposes that \emph{no} occurrences of the
  term should be affected by the tactic. The tactic:
\begin{lstlisting}
  set x := {-}(f 2).
\end{lstlisting}
leaves the goal unchanged and adds the definition \ssrC{x := f 2} to the
context. This kind of tactic may be used to take advantage of the
power of the matching algorithm in a local definition, instead of
copying large terms by hand.
\end{itemize}


It is important to remember that matching \emph{precedes} occurrence
selection, hence the tactic:
\begin{lstlisting}
  set a := {2}(_ + _).
\end{lstlisting}
transforms the goal \ssrC{x + y = x + y + z} into \ssrC{x + y = a + z}
and fails on the goal \\
\ssrC{(x + y) + (z + z) = z + z} with the error message:
\begin{lstlisting}
  User error: only 1 < 2 occurrence of (x + y + (z + z))
\end{lstlisting}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Localization}\label{ssec:loc}


It is possible to define an abbreviation for a term appearing in the
context of a goal thanks to the \ssrC{in} tactical.

A tactic of the form:

\begin{center}
  \ssrC{set x :=} {\term} \ssrC{in} \ssrN[1]{fact}\ssrC{...}\ssrN[n]{fact}.
\end{center}

introduces a defined constant called \ssrC{x} in the context, and folds
it in the facts \textit{fact$_1 \dots$ fact$_n$}
The body of \ssrC{x} is the first subterm matching \textit{term} in
\textit{fact$_1 \dots$ fact$_n$}.

A tactic of the form:

\begin{center}
  \ssrC{set x :=} {\term} \ssrC{in} \ssrN[1]{fact}\ssrC{...}\ssrN[n]{fact} \ssrC{*.}
\end{center}

matches {\term} and then folds \ssrC{x} similarly in
\textit{fact$_1 \dots$ fact$_n$}, but also folds \ssrC{x} in the goal.

A goal \ssrL-x + t = 4-, whose context contains \ssrC{Hx : x = 3}, is left
unchanged by the tactic:
\begin{lstlisting}
  set z := 3 in Hx.
\end{lstlisting}
but the context is extended with the definition \ssrC{z := 3} and \ssrC{Hx} becomes
\ssrC{Hx : x = z}.
On the same goal and context, the tactic:
\begin{lstlisting}
  set z := 3 in Hx *.
\end{lstlisting}
will moreover change the goal into \ssrL-x + t = S z-. Indeed, remember
that \ssrC{4} is just a notation for \ssrC{(S 3)}.

The use of the \ssrC{in} tactical is not limited to the localization of
abbreviations: for a complete description of the \ssrC{in} tactical, see
section \ref{ssec:profstack}.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Basic tactics}\label{sec:book}



A sizable fraction of proof scripts consists of steps that do not
"prove" anything new, but instead perform menial bookkeeping tasks
such as selecting the names of constants and assumptions or splitting
conjuncts. Although they are logically trivial, bookkeeping steps are
extremely important because they define the structure of the data-flow
of a proof script. This is especially true for reflection-based
proofs, which often involve large numbers of constants and
assumptions.  Good bookkeeping consists in always explicitly declaring
(i.e., naming) all new constants and assumptions in the script, and
systematically pruning irrelevant constants and assumptions in the
context. This is essential in the context of an interactive
development environment (IDE), because it facilitates navigating the
proof, allowing to instantly "jump back" to the point at which a
questionable assumption was added, and to find relevant assumptions by
browsing the pruned context.  While novice or casual \Coq{} users may
find the automatic name selection feature convenient, the usage of
such a feature severely undermines the readability and maintainability
of proof scripts, much like automatic variable declaration in programming
languages. The \ssr{} tactics are therefore designed to support
precise bookkeeping and to eliminate name generation heuristics.
The bookkeeping features of \ssr{} are implemented as tacticals (or
pseudo-tacticals), shared across most \ssr{} tactics, and thus form
the foundation of the \ssr{} proof language.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Bookkeeping}\label{ssec:profstack}
\idx{move: \dots{}}
\idx{move=> \dots{}}
\idx{move: \dots{} => \dots{}}
\idx{\dots{} in \dots{}}

During the course of a proof \Coq{} always present the user with
a \emph{sequent} whose general form is
\begin{displaymath}\begin{array}{l}
%\arrayrulecolor{dkviolet}
c_i\ \ssrC{:}\ T_i \\
\dots\\
d_j\ \ssrC{:=}\ e_j\ \ssrC{:}\ T_j \\
\dots\\
F_k\ \ssrC{:}\ P_k \\
\dots \\[3pt]
\hline\hline\\[-8pt]
\ssrC{forall}\ \ssrC{(}x_\ell\ \ssrC{:}\ T_\ell\ssrC{)}\ \dots,\\
\ssrC{let}\ y_m\ \ssrC{:=}\ b_m\ \ssrC{in}\ \dots\ \ssrC{in}\\
P_n\ \ssrC{->}\ \dots\ \ssrC{->}\ C
\end{array}\end{displaymath}
The \emph{goal} to be proved appears below the double line; above the line is
the \emph{context} of the sequent, a set of declarations of
\emph{constants}~$c_i$, \emph{defined constants}~$d_i$, and
\emph{facts}~$F_k$ that can be used to prove the goal (usually, $T_i,
T_j\;:\;\ssrC{Type}$ and $P_k\;:\;\ssrC{Prop}$). The various kinds of
declarations can come in any order. The top part of the context
consists of declarations produced by the \ssrC{Section} commands
\ssrC{Variable}, \ssrC{Let}, and \ssrC{Hypothesis}. This \emph{section context}
is never affected by the \ssr{} tactics: they only operate on
the lower part --- the \emph{proof context}.
As in the figure above, the goal often decomposes into a series of
(universally) quantified \emph{variables}
$\ssrC{(}x_\ell\;\ssrC{:}\;T_\ell\ssrC{)}$, local \emph{definitions}
$\ssrC{let}\;y_m\:\ssrC{:=}\;b_m\;\ssrC{in}$, and \emph{assumptions}
$P_n\;\ssrC{->}$, and a \emph{conclusion}~$C$ (as in the context, variables,
definitions, and assumptions can appear in any order). The conclusion
is what actually needs to be proved --- the rest of the goal can be
seen as a part of the proof context that happens to be ``below the line''.

However, although they are logically equivalent, there are fundamental
differences between constants and facts on the one hand, and variables
and assumptions on the others. Constants and facts are
\emph{unordered}, but \emph{named} explicitly in the proof text;
variables and assumptions are \emph{ordered}, but \emph{unnamed}: the
display names of variables may change at any time because of
$\alpha$-conversion.

Similarly, basic deductive steps such as \ssrC{apply} can only operate on
the goal because the Gallina terms that control their action (e.g.,
the type of the lemma used by \ssrC{apply}) only provide unnamed bound
variables.\footnote{Thus scripts that depend on bound variable names, e.g.,
via \ssrC{intros} or \ssrC{with}, are inherently fragile.}  Since the proof
script can only refer directly to the context, it must constantly
shift declarations from the goal to the context and conversely in
between deductive steps.

In \ssr{} these moves are performed by two \emph{tacticals} `\ssrC{=>}'
and `\ssrC{:}', so that the bookkeeping required by a deductive step can
be directly associated to that step, and that tactics in an \ssr{}
script correspond to actual logical steps in the proof rather than
merely shuffle facts. Still, some isolated bookkeeping is unavoidable,
such as naming variables and assumptions at the beginning of a proof.
\ssr{} provides a specific \ssrC{move} tactic for this purpose.

Now \ssrC{move} does essentially nothing: it is mostly a placeholder for
`\ssrC{=>}' and `\ssrC{:}'. The `\ssrC{=>}' tactical moves variables, local
definitions, and assumptions to the context, while the `\ssrC{:}'
tactical moves facts and constants to the goal. For example, the proof
of\footnote{The name \ssrC{subnK} reads as
``right cancellation rule for \ssrC{nat} subtraction''.}
\begin{lstlisting}
  Lemma |*subnK*| : forall m n, n <= m -> m - n + n = m.
\end{lstlisting}\noindent
might start with
\begin{lstlisting}
  move=> m n le_n_m.
\end{lstlisting}
where \ssrC{move} does nothing, but \ssrL|=> m n le_m_n| changes the
variables and assumption of the goal in the constants \ssrC{m n : nat}
and the fact \ssrL|le_n_m : n <= m|, thus exposing the conclusion\\
 \ssrC{m - n + n = m}. 

The `\ssrC{:}' tactical is the converse of `\ssrC{=>}': it removes facts
and constants from the context by turning them into variables and assumptions.
Thus
\begin{lstlisting}
  move: m le_n_m.
\end{lstlisting}
turns back \ssrC{m} and \ssrL|le_m_n| into a variable and an assumption, removing
them from the proof context, and changing the goal to
\begin{lstlisting}
  forall m, n <= m -> m - n + n = m.
\end{lstlisting}
which can be proved by induction on \ssrC{n} using \ssrC{elim: n}.

\noindent
Because they are tacticals, `\ssrC{:}' and `\ssrC{=>}' can be combined, as in
\begin{lstlisting}
  move: m le_n_m => p le_n_p.
\end{lstlisting}
simultaneously renames \ssrL|m| and \ssrL|le_m_n| into \ssrL|p| and \ssrL|le_n_p|,
respectively, by first turning them into unnamed variables, then
turning these variables back into constants and facts.

Furthermore, \ssr{} redefines the basic \Coq{} tactics \ssrC{case},
\ssrC{elim}, and \ssrC{apply} so that they can take better advantage of
'\ssrC{:}' and `\ssrC{=>}'. In there \ssr{} variants, these tactic operate
on the first  variable or constant of the goal and they do not use or
change the proof context. The `\ssrC{:}' tactical is used to operate on
an element in the context. For instance the proof of \ssrC{subnK} could
continue with
\begin{lstlisting}
  elim: n.
\end{lstlisting}
instead of \ssrC{elim n}; this has the advantage of
removing \ssrC{n} from the context. Better yet, this \ssrC{elim} can be combined
with previous \ssrC{move} and with the branching version of the \ssrC{=>} tactical
(described in~\ref{ssec:intro}),
to encapsulate the inductive step in a single command:
\begin{lstlisting}
  elim: n m le_n_m => [|n IHn] m => [_ | lt_n_m].
\end{lstlisting}
which breaks down the proof into two subgoals,
\begin{lstlisting}
  m - 0 + 0 = m
\end{lstlisting}
given \ssrC{m : nat}, and
\begin{lstlisting}
  m - S n + S n = m
\end{lstlisting}
given \ssrC{m n : nat}, \ssrL|lt_n_m : S n <= m|, and
\begin{lstlisting}
  IHn : forall m, n <= m -> m - n + n = m.
\end{lstlisting}
The '\ssrC{:}' and `\ssrC{=>}' tacticals can be explained very simply
if one views the goal as a stack of variables and assumptions piled
on a conclusion:
\begin{itemize}
\item {\tac} \ssrC{:} $a$ $b$ $c$ pushes the context constants $a$, $b$, $c$
as goal variables \emph{before} performing {\tac}.
\item {\tac} \ssrC{=>} $a$ $b$ $c$ pops the top three goal variables as
context constants $a$, $b$, $c$, \emph{after} {\tac}
has been performed.
\end{itemize}
These pushes and pops do not need to balance out as in the examples above,
so
\begin{lstlisting}
  move: m le_n_m => p.
\end{lstlisting}
would rename \ssrC{m} into \ssrC{p}, but leave an extra assumption \ssrC{n <= p}
in the goal.

Basic tactics like \ssrC{apply} and \ssrC{elim} can also be used without the
'\ssrC{:}' tactical: for example we can directly start a proof of \ssrC{subnK}
by induction on the top variable \ssrC{m} with
\begin{lstlisting}
  elim=> [|m IHm] n le_n.
\end{lstlisting}

\noindent
The general form of the localization tactical \ssrC{in} is also best
explained in terms of the goal stack:

\begin{center}
  {\tac} \ssrC{in a H1 H2 *.}
\end{center}

is basically equivalent to

\begin{center}
  \ssrC{move: a H1 H2;} {\tac} \ssrC{=> a H1 H2.}
\end{center}

with two differences: the \ssrC{in} tactical will preserve the body of \ssrC{a} if
\ssrC{a} is a defined constant, and if the `\ssrC{*}' is omitted it
will use a temporary abbreviation to hide the statement of the goal
from \ssrC{/*tactic*/}.

The general form of the \ssrC{in} tactical can be used directly with
the \ssrC{move}, \ssrC{case} and \ssrC{elim} tactics, so that one can write
\begin{lstlisting}
  elim: n => [|n IHn] in m le_n_m *.
\end{lstlisting}
instead of
\begin{lstlisting}
  elim: n m le_n_m => [|n IHn] m le_n_m.
\end{lstlisting}
This is quite useful for inductive proofs that involve many facts.

\noindent See section \ref{ssec:gloc} for the general syntax and presentation
of the \ssrC{in} tactical.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The defective tactics}\label{ssec:basictac}

In this section we briefly present the three basic tactics performing
context manipulations and the main backward chaining tool.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{move} tactic.}\label{sssec:move}
\idx{move}

The \ssrC{move} tactic, in its
defective form, behaves like the primitive \ssrC{hnf} \Coq{} tactic. For
example, such a defective:
\begin{lstlisting}
  move.
\end{lstlisting}
exposes the first assumption in the goal, i.e. its changes the goal
\ssrC{\~ False} into \ssrC{False -> False}.

More precisely, the \ssrC{move} tactic inspects the goal and does nothing
(\ssrC{idtac}) if an introduction step is possible, i.e. if the
goal is a product or a \ssrC{let}$\dots$\ssrC{in}, and performs \ssrC{hnf}
otherwise.

Of course this tactic is most often used in combination with the
bookkeeping tacticals (see section \ref{ssec:intro} and
\ref{ssec:discharge}). These combinations mostly subsume the \ssrC{intros},
\ssrC{generalize}, \ssrC{revert}, \ssrC{rename}, \ssrC{clear} and
\textcolor{dkblue}{\texttt{pattern}} tactics.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{case} tactic.}
\idx{case: \dots{}}

The \ssrC{case} tactic performs
\emph{primitive case analysis} on (co)inductive types; specifically,
it destructs the top variable or assumption of the goal,
exposing its constructor(s) and its arguments, as well as setting the value
of its type family indices if it belongs to a type family
(see section \ref{ssec:typefam}).

The \ssr{} \ssrC{case} tactic has a special behavior on
equalities.
If the top assumption of the goal is an equality, the \ssrC{case} tactic
``destructs'' it as a set of equalities between the constructor
arguments of its left and right hand sides, as per the
tactic \ssrC{injection}.
For example, \ssrC{case} changes the goal
\begin{lstlisting}
  (x, y) = (1, 2) -> G.
\end{lstlisting}
into
\begin{lstlisting}
  x = 1 -> y = 2 -> G.
\end{lstlisting}

Note also that the case of \ssr{} performs \ssrC{False}
elimination, even if no branch is generated by this case operation.
Hence the command:
\begin{lstlisting}
  case.
\end{lstlisting}
on a goal of the form \ssrC{False -> G} will succeed and prove the goal.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{elim} tactic.} 
\idx{elim: \dots{}}

The \ssrC{elim} tactic performs
inductive elimination on inductive types.
The defective:
\begin{lstlisting}
  elim.
\end{lstlisting}
tactic performs inductive elimination on a goal whose top assumption
has an inductive type. For example on goal of the form:
\begin{lstlisting}
  forall n : nat, m <= n
\end{lstlisting}
 in a context containing \ssrC{m : nat}, the
\begin{lstlisting}
  elim.
\end{lstlisting}
tactic produces two goals,
\begin{lstlisting}
  m <=  0
\end{lstlisting}
on one hand and
\begin{lstlisting}
  forall n : nat, m <= n -> m <= S n
\end{lstlisting}
on the other hand.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{apply} tactic.}\label{sssec:apply}
\idx{apply: \dots{}}

The \ssrC{apply} tactic is the main
backward chaining tactic of the proof system. It takes as argument any
\ssrC{/*term*/} and applies it to the goal.
Assumptions in the type of \ssrC{/*term*/} that don't directly match the
goal may generate one or more subgoals.

In fact the \ssr{} tactic:
\begin{lstlisting}
  apply.
\end{lstlisting}
is a synonym for:
\begin{lstlisting}
  intro top; first [refine top | refine (top _) |  refine (top _ _) | ...]; clear top.
\end{lstlisting}
where \ssrC{top} is fresh name, and the sequence of \ssrC{refine} tactics
tries to catch the appropriate number of wildcards to be inserted.
Note that this use of the \ssrC{refine} tactic implies that the tactic
tries to match the goal up to expansion of
constants and evaluation of subterms.

\ssr{}'s \ssrC{apply} has a special behaviour on goals containing
existential metavariables of sort \ssrC{Prop}.  Consider the
following example:
\begin{lstlisting}
Goal (forall y, 1 < y -> y < 2 -> exists x : { n | n < 3 }, proj1_sig x > 0).
move=> y y_gt1 y_lt2; apply: (ex_intro _ (exist _ y _)).
  by apply: gt_trans _ y_lt2.
by move=> y_lt3; apply: lt_trans y_gt1.
\end{lstlisting}
Note that the last \ssrC{_} of the tactic \ssrC{apply: (ex_intro _ (exist _ y _))}
represents a proof that \ssrC{y < 3}. Instead of generating the following
goal
\begin{lstlisting}
   0 <  (n:=3) (m:=y) ?54
\end{lstlisting}
\noindent the system tries to prove \ssrC{y < 3} calling the \ssrC{trivial}
tactic. If it succeeds, let's say because the context contains
\ssrC{H : y < 3}, then the system generates the following goal:
\begin{lstlisting}
   0 < proj1_sig (exist (fun n => n < 3) y H
\end{lstlisting}
\noindent Otherwise the missing proof is considered to be irrelevant, and
is thus discharged generating the following goals:
\begin{lstlisting}
   y < 3
   forall H : y < 3, proj1_sig (exist (fun n => n < 3) y H)
\end{lstlisting}
Last, the user can replace the \ssrC{trivial} tactic by defining
an Ltac expression named \ssrC{ssrautoprop}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Discharge}\label{ssec:discharge}
\idx{\dots{} : \dots{}}

The general syntax of the discharging tactical `\ssrC{:}' is:
\begin{center}
	{\tac} \optional{\ssrN{ident}} \ssrC{:} \ssrN[1]{d-item} $\dots$ \ssrN[n]{d-item} \optional{\ssrN{clear-switch}}
\end{center}
where $n > 0$, and \ssrN{d-item} and \ssrN{clear-switch} are defined as
\begin{longtable}{rcl}
\ssrN{d-item} & ::= & \optional{\ssrN{occ-switch} {\optsep} \ssrN{clear-switch}} {\term} \\
\ssrN{clear-switch}& ::=& \ssrC{\{} \ssrN[1]{ident}\, \ldots\,  \ssrN[m]{ident} \ssrC{\}}
\end{longtable}
with the following requirements:
\begin{itemize}
\item {\tac} must be one of the four basic tactics described
      in~\ref{ssec:basictac}, i.e., \ssrC{move}, \ssrC{case}, \ssrC{elim} or \ssrC{apply},
      the \ssrC{exact} tactic (section \ref{ssec:termin}),
      the \ssrC{congr} tactic (section \ref{ssec:congr}), or the application
      of the \emph{view} tactical `\ssrC{/}' (section \ref{ssec:assumpinterp})
      to one of \ssrC{move}, \ssrC{case}, or \ssrC{elim}.
\item The optional \ssrN{ident} specifies \emph{equation generation}
      (section \ref{ssec:equations}), and is only allowed if {\tac}
      is \ssrC{move}, \ssrC{case} or \ssrC{elim}, or the application of the
      view tactical `\ssrC{/}' (section \ref{ssec:assumpinterp})
      to \ssrC{case} or \ssrC{elim}.
\item An \ssrN{occ-switch} selects occurrences of {\term},
      as in \ref{sssec:occselect}; \ssrN{occ-switch} is not allowed if
      {\tac} is \ssrC{apply} or \ssrC{exact}.
\item A clear item \ssrN{clear-switch} specifies facts and constants to be
  deleted from the proof context (as per the \ssrC{clear} tactic).
\end{itemize}
The `\ssrC{:}' tactical first \emph{discharges} all the \ssrN{d-item}s,
right to left, and then performs {\tac}, i.e., for each \ssrN{d-item},
starting with $\ssrN[n]{d-item}$:
\begin{enumerate}
\item The \ssr{} matching algorithm described in section~\ref{ssec:set}
      is used to find occurrences of {\term} in the goal,
      after filling any holes `\ssrC{_}' in {\term}; however if {\tac}
      is \ssrC{apply} or \ssrC{exact} a different matching algorithm,
      described below, is used
      \footnote{Also, a slightly different variant may be used for the first
      \ssrN{d-item} of \ssrC{case} and \ssrC{elim}; see section~\ref{ssec:typefam}.}.
\item~\label{enum:gen} These occurrences are replaced by a new
  variable; in particular,
      if {\term} is a fact, this adds an assumption to the goal.
\item~\label{enum:clr} If {\term} is \emph{exactly} the name of a constant
      or fact in the proof context, it is deleted from the context,
      unless there is an \ssrN{occ-switch}.
\end{enumerate}
Finally, {\tac} is performed just after $\ssrN[1]{d-item}$ has been
generalized ---
that is, between steps \ref{enum:gen} and \ref{enum:clr} for $\ssrN[1]{d-item}$.
The names listed in the final \ssrN{clear-switch} (if it is present)
are cleared first, before $\ssrN[n]{d-item}$ is discharged.

\noindent
Switches affect the discharging of a \ssrN{d-item} as follows:
\begin{itemize}
\item An \ssrN{occ-switch} restricts generalization (step~\ref{enum:gen})
      to a specific subset of the occurrences of {\term}, as per
      \ref{sssec:occselect}, and prevents clearing (step~\ref{enum:clr}).
\item All the names specified by a \ssrN{clear-switch} are deleted from the
      context in step~\ref{enum:clr}, possibly in addition to {\term}.
\end{itemize}
For example, the tactic:
\begin{lstlisting}
  move: n {2}n (refl_equal n).
\end{lstlisting}
\begin{itemize}
\item first generalizes \ssrC{(refl_equal n : n = n)};
\item then generalizes the second occurrence of \ssrC{n}.
\item finally generalizes all the other occurrences of \ssrC{n},
      and clears \ssrC{n} from the proof context
      (assuming \ssrC{n} is a proof constant).
\end{itemize}
Therefore this tactic changes any goal \ssrC{G} into
\begin{lstlisting}
 forall n n0 : nat, n = n0 -> G.
\end{lstlisting}
where the name \ssrC{n0} is picked by the \Coq{} display function,
and assuming \ssrC{n} appeared only in~\ssrC{G}.

Finally, note that a discharge operation generalizes defined constants
as variables, and not as local definitions. To override this behavior,
prefix the name of the local definition with a \ssrC{@},
like in \ssrC{move: @n}.

This is in contrast with the behavior of the \ssrC{in} tactical (see section
\ref{ssec:gloc}), which preserves local definitions by default.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Clear rules}

The clear step will fail if {\term} is a proof constant that
appears in other facts; in that case either the facts should be
cleared explicitly with a \ssrN{clear-switch}, or the clear step should be
disabled. The latter can be done by adding an \ssrN{occ-switch} or simply by
putting parentheses around {\term}: both
\begin{lstlisting}
  move: (n).
\end{lstlisting}
and
\begin{lstlisting}
  move: {+}n.
\end{lstlisting}
generalize \ssrC{n} without clearing \ssrC{n} from the proof context.

The clear step will also fail if the \ssrN{clear-switch} contains a
\ssrN{ident} that is not in the \emph{proof} context.
Note that \ssr{} never clears a section constant.

If {\tac} is \ssrC{move} or \ssrC{case} and an equation \ssrN{ident} is given,
then clear (step~\ref{enum:clr}) for $\ssrN[1]{d-item}$ is suppressed
(see section \ref{ssec:equations}).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Matching for \ssrC{apply} and \ssrC{exact}}\label{sss:strongapply}

The matching algorithm for \ssrN{d-item}s of the \ssr{} \ssrC{apply} and
\ssrC{exact} tactics
exploits the type of $\ssrN[1]{d-item}$ to interpret
wildcards in the other \ssrN{d-item} and to determine which occurrences of
these should be generalized.
Therefore, \ssrN{occur switch}es are not needed for \ssrC{apply} and \ssrC{exact}.

Indeed, the \ssr{} tactic \ssrC{apply: H x} is equivalent to
\begin{lstlisting}
  refine (@H _ ... _ x); clear H x
\end{lstlisting}
with an appropriate number of wildcards between \ssrC{H} and~\ssrC{x}.

Note that this means that matching for \ssrC{apply} and \ssrC{exact} has
much more context to interpret wildcards; in particular it can accommodate
the `\ssrC{_}' \ssrN{d-item}, which would always be rejected after `\ssrC{move:}'.
For example, the tactic
\begin{lstlisting}
  apply: trans_equal (Hfg _) _.
\end{lstlisting}
transforms the goal \ssrC{f a = g b}, whose context contains
\ssrC{(Hfg : forall x, f x = g x)}, into \ssrC{g a = g b}.
This tactic is equivalent (see section \ref{ssec:profstack}) to:
\begin{lstlisting}
  refine (trans_equal (Hfg _) _).
\end{lstlisting}
and this is a common idiom for applying transitivity on the left hand side
of an equation.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{abstract} tactic}\label{ssec:abstract}
\idx{abstract: \dots{}}

The \ssrC{abstract} tactic assigns an abstract constant previously introduced with
the \ssrC{[: name ]} intro pattern (see section~\ref{ssec:intro},
page~\pageref{ssec:introabstract}).
In a goal like the following:
\begin{lstlisting}
 m : nat
 abs : <hidden>
 n : nat
 =============
 m < 5 + n
\end{lstlisting}
The tactic \ssrC{abstract: abs n} first generalizes the goal with respect to
\ssrC{n} (that is not visible to the abstract constant \ssrC{abs}) and then
assigns \ssrC{abs}.  The resulting goal is:
\begin{lstlisting}
 m : nat
 n : nat
 =============
 m < 5 + n
\end{lstlisting}
Once this subgoal is closed, all other goals having \ssrC{abs} in their context
see the type assigned to \ssrC{abs}.  In this case:
\begin{lstlisting}
 m : nat
 abs : forall n, m < 5 + n
\end{lstlisting}

For a more detailed example the user should refer to section~\ref{sssec:have},
page~\pageref{sec:havetransparent}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Introduction}\label{ssec:intro}
\idx{\dots{} => \dots{}}

The application of a tactic to a given goal can generate
(quantified) variables, assumptions, or definitions, which the user may want to
\emph{introduce} as new facts, constants or defined constants, respectively.
If the tactic splits the goal into several subgoals,
each of them may require the introduction of different constants and facts.
Furthermore it is very common to immediately decompose
or rewrite with an assumption instead of adding it to the context,
as the goal can often be simplified and even
proved after this.

All these operations are performed by the introduction tactical
`\ssrC{=>}', whose general syntax is
\begin{center}
	{\tac} \ssrC{=>} \ssrN[1]{i-item} $\dots$ \ssrN[n]{i-item}
\end{center}
where {\tac} can be any tactic, $n > 0$ and
\begin{longtable}{rcl}
  \ssrN{i-item}& ::=& \ssrN{i-pattern} {\optsep} \ssrN{s-item} {\optsep} \ssrN{clear-switch} {\optsep} \ssrC{/}{\term} \\
  \ssrN{s-item}& ::=& \ssrC{/=} {\optsep} \ssrC{//} {\optsep} \ssrC{//=} \\
  \ssrN{i-pattern}& ::=& \ssrN{ident} {\optsep} \ssrC{_} {\optsep} \ssrC{?} {\optsep} \ssrC{*} {\optsep} \optional{\ssrN{occ-switch}}\ssrC{->} {\optsep} \optional{\ssrN{occ-switch}}\ssrC{<-} {\optsep} \\
	   &&      \ssrC{[} \ssrN[1]{i-item}$^*$ \ssrC{|} $\dots$ \ssrC{|} \ssrN[m]{i-item}$^*$ \ssrC{]} {\optsep} \ssrC{-} {\optsep} \ssrC{[:} \ssrN{ident}$^+$ \ssrC{]}
\end{longtable}

The `\ssrC{=>}' tactical first executes {\tac}, then the
\ssrN{i-item}s, left to right, i.e., starting from $\ssrN[1]{i-item}$.  An
\ssrN{s-item} specifies a simplification operation; a $\ssrN{clear
switch}$ specifies context pruning as in~\ref{ssec:discharge}. The
\ssrN{i-pattern}s can be seen as a variant of \emph{intro patterns}~\ref{intros-pattern}:
each performs an introduction operation, i.e., pops some variables or
assumptions from the goal.

An \ssrN{s-item} can simplify the set of subgoals or the subgoal themselves:
\begin{itemize}
\item \ssrC{//} removes all the ``trivial'' subgoals that can be resolved by
      the \ssr{} tactic \ssrC{done} described in~\ref{ssec:termin}, i.e., it
      executes \ssrC{try done}.
\item \ssrC{/=} simplifies the goal by performing partial evaluation, as
   per the tactic \ssrC{simpl}.\footnote{Except \ssrC{/=} does not
   expand the local definitions created by the \ssr{} \ssrC{in} tactical.}
\item \ssrC{//=} combines both kinds of simplification; it is equivalent
    to \ssrC{/= //}, i.e., \ssrC{simpl; try done}.
\end{itemize}
When an \ssrN{s-item} bears a \ssrN{clear-switch}, then the \ssrN{clear-switch} is
executed \emph{after} the \ssrN{s-item}, e.g., \ssrL|{IHn}//| will solve
some subgoals, possibly using the fact \ssrL|IHn|, and will erase \ssrL|IHn|
from the context of the remaining subgoals.

The last entry in the \ssrN{i-item} grammar rule, \ssrC{/}{\term},
represents a view (see section~\ref{sec:views}). If $\ssrN[k+1]{i-item}$
is a view \ssrN{i-item}, the view is applied to the assumption in top
position once $\ssrN[1]{i-item} \dots \ssrN[k]{i-item}$ have been performed.

The view is applied to the top assumption.

\ssr{} supports the following \ssrN{i-pattern}s:
\begin{itemize}
\item \ssrN{ident} pops the top variable, assumption, or local definition into
      a new constant, fact, or defined constant \ssrN{ident}, respectively.
      Note that defined constants cannot be introduced when
      $\delta$-expansion is required to expose the top variable or assumption.
\item \ssrC{?} pops the top variable into an anonymous constant or fact,
      whose name is picked by the tactic interpreter.
      \ssr{} only generates names that
      cannot appear later in the user script.\footnote{\ssr{} reserves
      all identifiers of the form ``\ssrC{_x_}'', which is used for such
      generated names.}
\item \ssrC{_} pops the top variable into an anonymous constant that will be
     deleted from
     the proof context of all the subgoals produced by the \ssrC{=>} tactical.
     They should thus never be displayed, except in an error message
     if the constant is still actually used in the goal or context after
     the last \ssrN{i-item} has been executed (\ssrN{s-item}s can erase goals
     or terms where the constant appears).
\item \ssrC{*} pops all the remaining apparent variables/assumptions
     as anonymous constants/facts. Unlike \ssrC{?} and \ssrC{move} the \ssrC{*}
     \ssrN{i-item} does not expand definitions in the goal to expose
     quantifiers, so it may be useful to repeat a \ssrC{move=> *} tactic,
     e.g., on the goal
\begin{lstlisting}
  forall a b : bool, a <> b
\end{lstlisting}
a first \ssrC{move=> *} adds only \ssrC{_a_ : bool} and \ssrC{_b_ : bool} to
the context; it takes a second \ssrC{move=> *} to add
\ssrC{_Hyp_ : _a_ = _b_}.
\item $[\ssrN{occ-switch}]$\ssrC{->} (resp. $[\ssrN{occ-switch}]$\ssrC{<-})
  pops the top assumption
  (which should be a rewritable proposition) into an anonymous fact,
  rewrites (resp. rewrites right to left) the goal with this fact
  (using the \ssr{} \ssrC{rewrite} tactic described in section~\ref{sec:rw},
  and honoring the optional occurrence selector),
  and finally deletes the anonymous fact from the context.
\item\ssrC{[ $\ssrN[1]{i-item}^*$ | $\dots$ | $\ssrN[m]{i-item}^*$ ]},
   when it is the very \emph{first} \ssrN{i-pattern} after ${\tac}\;\ssrC{=>}$
   tactical \emph{and} {\tac} is not a \ssrC{move}, is a \emph{branching}
   \ssrN{i-pattern}. It executes
   the sequence $\ssrN[i]{i-item}^*$ on the $i^{\rm th}$
   subgoal produced by {\tac}. The execution of {\tac}
   should thus generate exactly $m$
   subgoals, unless the \ssrC{[$\dots$]} \ssrN{i-pattern} comes after an initial
   \ssrC{//} or \ssrC{//=} \ssrN{s-item} that closes some of the goals produced by
   {\tac}, in which case exactly $m$ subgoals should remain after the
   \ssrN{s-item}, or we have the trivial branching \ssrN{i-pattern} \ssrC{[]},
   which always does nothing, regardless of the number of remaining subgoals.
\item\ssrC{[ $\ssrN[1]{i-item}^*$ | $\dots$ | $\ssrN[m]{i-item}^*$ ]}, when it is
   \emph{not} the first \ssrN{i-pattern} or when {\tac} is a
   \ssrC{move}, is a \emph{destructing} \ssrN{i-pattern}.  It starts by
   destructing the top variable, using the \ssr{} \ssrC{case} tactic
   described in~\ref{ssec:basictac}.  It then behaves as the
   corresponding branching \ssrN{i-pattern}, executing the sequence
   $\ssrN[i]{i-item}^*$ in the $i^{\rm th}$ subgoal generated by the case
   analysis; unless we have the trivial destructing \ssrN{i-pattern}
   \ssrC{[]}, the latter should generate exactly $m$ subgoals, i.e., the
   top variable should have an inductive type with exactly $m$
   constructors.\footnote{More precisely, it should have a quantified
   inductive type with $a$ assumptions and $m - a$ constructors.}
   While it is good style to use the $\ssrN[i]{i-item}^*$
   to pop the variables and assumptions corresponding to each constructor,
   this is not enforced by \ssr{}.
\item\ssrC{-} does nothing, but counts as an intro pattern. It can also
  be used to force the interpretation of
  \ssrC{[ $\ssrN[1]{i-item}^*$ | $\dots$ | $\ssrN[m]{i-item}^*$ ]}
   as a case analysis like in \ssrC{move=> -[H1 H2]}. It can also be used
   to indicate explicitly the link between a view and a name like in
   \ssrC{move=> /eqP-H1}. Last, it can serve as a separator between
   views. Section~\ref{ssec:multiview} explains in which respect
   the tactic \ssrC{move=> /v1/v2} differs from the tactic
   \ssrC{move=> /v1-/v2}.
\item\ssrC{[: $\ssrN{ident}^+$ ]} introduces in the context an abstract constant
   for each \ssrN{ident}.  Its type has to be fixed later on by using
   the \ssrC{abstract} tactic (see page~\pageref{ssec:abstract}).  Before then
   the type displayed is \ssrC{<hidden>}.\label{ssec:introabstract}
\end{itemize}
Note that \ssr{} does not support the syntax
$\ssrC{(}\ssrN{ipat}\ssrC{,}\dots\ssrC{,}\ssrN{ipat}\ssrC{)}$ for destructing
intro-patterns.

Clears are deferred until the end of the intro pattern. For
example, given the goal:
\begin{lstlisting}
x, y : nat
==================
0 < x = true -> (0 < x) && (y < 2) = true
\end{lstlisting}
the tactic \ssrC{move=> \{x\} ->} successfully rewrites the goal and
deletes \ssrC{x} and the anonymous equation. The goal is thus turned into:
\begin{lstlisting}
y : nat
==================
true && (y < 2) = true
\end{lstlisting}
If the cleared names are reused in the same intro pattern, a renaming
is performed behind the scenes.

Facts mentioned in a clear switch must be valid
names in the proof context (excluding the section context).

The rules for interpreting branching and destructing \ssrN{i-pattern}
are motivated by the fact that it would be pointless to have a branching
pattern if {\tac} is a \ssrC{move}, and in most of the remaining cases
{\tac} is \ssrC{case} or \ssrC{elim}, which implies destruction.
The rules above imply that
\begin{lstlisting}
  move=> [a b].
  case=> [a b].
  case=> a b.
\end{lstlisting}
are all equivalent, so which one to use is a matter of style;
\ssrC{move} should be used for casual decomposition,
such as splitting a pair, and \ssrC{case} should be used for actual decompositions,
in particular for type families (see~\ref{ssec:typefam})
and proof by contradiction.

The trivial branching \ssrN{i-pattern} can be used to force the branching
interpretation, e.g.,
\begin{lstlisting}
  case=> [] [a b] c.
  move=> [[a b] c].
  case;  case=> a b c.
\end{lstlisting}
are all equivalent.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Generation of equations}\label{ssec:equations}
\idx{move eq : \dots{}}

The generation of named equations option stores the definition of a
new constant as an equation. The tactic:
\begin{lstlisting}
  move En: (size l) => n.
\end{lstlisting}
where \ssrC{l} is a list, replaces \ssrC{size l} by \ssrC{n} in the goal and
adds the fact \ssrC{En : size l = n} to the context.
 This is quite different from:
\begin{lstlisting}
  pose n := (size l).
\end{lstlisting}
which generates a definition \ssrC{n := (size l)}. It is not possible to
generalize or
rewrite such a definition; on the other hand, it is automatically
expanded during
computation, whereas expanding the equation \ssrC{En} requires explicit
rewriting.

The use of this equation name generation option with a \ssrC{case} or an
\ssrC{elim} tactic changes the status of the first \iitem{}, in order to
deal with the possible parameters of the constants introduced.

On the
goal \ssrC{a <> b} where \ssrC{a, b} are natural numbers, the tactic:
\begin{lstlisting}
  case E : a => [|n].
\end{lstlisting}
generates two subgoals. The equation \ssrC{E : a = 0}  (resp. \ssrC{E : a =
  S n}, and the constant \ssrC{n : nat}) has been added to
the context of the goal \ssrC{0 <> b} (resp. \ssrC{S n  <> b}).

If the user does not provide a branching \iitem{} as first \iitem{},
or if the \iitem{} does not provide enough names for the arguments of
a constructor,
then the constants generated are introduced under fresh \ssr{} names.
For instance, on the goal \ssrC{a <> b}, the tactic:
\begin{lstlisting}
  case E : a => H.
\end{lstlisting}
also generates two subgoals, both requiring a proof of \ssrC{False}.
 The hypotheses \ssrC{E : a = 0} and
\ssrC{H : 0 = b} (resp. \ssrC{E : a = S _n_} and
\ssrC{H : S _n_ = b}) have been added to the context of the first
subgoal (resp. the second subgoal).

Combining the generation of named equations mechanism with the
\ssrC{case} tactic strengthens the power of a case analysis. On the other
hand, when combined with the \ssrC{elim} tactic, this feature is mostly
useful for
debug purposes, to trace the values of decomposed parameters and
pinpoint failing branches.

% This feature is also useful
% to analyse and debug generate-and-test style scripts that prove program
% properties by generating a large set of input patterns and uniformly
% solving the corresponding subgoals by computation and rewriting, e.g,

% \begin{lstlisting}
%   case: et => [|e' et]; first by case: s.
%   case: e => //; case: b; case: w.
% \end{lstlisting}
% If the above sequence fails, then it's easy enough to replace the line
% above with
% \begin{lstlisting}
%   case: et => [|e' et].
%   case Ds: s; case De: e => //; case Db: b; case Dw: w=> [|s' w'] //=.
% \end{lstlisting}
% Then the first subgoal that appears will be the failing one, and the
% equations \ssrC{Ds}, \ssrC{De}, \ssrC{Db}
% and \ssrC{Dw} will pinpoint its branch. When the constructors of
% the decomposed type have arguments (like \ssrC{w : (seq nat)}
% above) these need to be
% introduced in order to generate the equation, so there should
% always be an explicit \iitem{} (\ssrC{\[|s' w'\]} above) that
% assigns names to these arguments. If this \iitem{}
% is omitted the arguments are introduced with default
% name; this
% feature should be
% avoided except for quick debugging runs (it has some uses in complex tactic
% sequences, however).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Type families}\label{ssec:typefam}
\idx{case: \dots{} / \dots{}}

When the top assumption of a goal has an inductive type, two
specific operations are possible: the case analysis performed by the
\ssrC{case} tactic, and the application of an induction principle,
performed by the \ssrC{elim} tactic. When this top assumption has an
inductive type, which is moreover an instance of a type family, \Coq{}
may need help from the user to specify which occurrences of the parameters
of the type should be substituted.

A specific \ssrC{/} switch indicates the type family parameters of the
type of a \ditem{} immediately following this \ssrC{/} switch, using the
syntax:

\begin{center}
 \ssrC{[} \ssrC{case} {\optsep} \ssrC{elim} \ssrC{]:} \ssrN{d-item}$^+$ \ssrC{/} \ssrN{d-item}$^*$
\end{center}

The \ssrN{d-item}s on the right side of the \ssrC{/} switch are discharged
as described in section \ref{ssec:discharge}. The case analysis or
elimination will be done on the type of the top assumption after these
discharge operations.

Every \ssrN{d-item} preceding the \ssrC{/} is interpreted as arguments of this
type, which should be an instance of an inductive type family. These terms are
not actually generalized, but rather selected for substitution. Occurrence
switches can be used to restrict the substitution.  If a {\term} is left
completely implicit (e.g. writing just $\ssrC{\_}$), then a pattern is inferred
looking at the type of the top assumption.  This allows for the compact syntax
\ssrC{case: \{2\}\_ / eqP}, were \ssrC{\_} is interpreted as \ssrC{(\_ == \_)}. Moreover
if the \ssrN{d-item}s list is too short, it is padded with an initial
sequence of $\ssrC{\_}$ of the right length.

Here is a small example on lists. We define first a function which
adds an element at the end of a given list.
\begin{lstlisting}
  Require Import List.

  Section LastCases.
  Variable A : Type.

  Fixpoint |*add_last*|(a : A)(l : list A): list A :=
  match l with
    |nil => a :: nil
    |hd :: tl => hd :: (add_last a tl)
  end.
\end{lstlisting}
Then we define an inductive predicate for
case analysis on lists according to their last element:
\begin{lstlisting}
  Inductive |*last_spec*| : list A -> Type :=
    | LastSeq0 : last_spec nil
    | LastAdd s x : last_spec (add_last x s).

  Theorem |*lastP*| : forall l : list A, last_spec l.
\end{lstlisting}
Applied to the goal:
\begin{lstlisting}
  Goal forall l : list A, (length l) * 2 = length (app l l).
\end{lstlisting}
the command:
\begin{lstlisting}
  move=> l; case: (lastP l).
\end{lstlisting}
generates two subgoals:
\begin{lstlisting}
  length nil * 2 = length (nil ++ nil)
\end{lstlisting}
and
\begin{lstlisting}
  forall (s : list A) (x : A),
    length (add_last x s) * 2 = length (add_last x s ++ add_last x s)
\end{lstlisting}
both having \ssrC{l : list A} in their context.

Applied to the same goal, the command:
\begin{lstlisting}
  move=> l; case: l / (lastP l).
\end{lstlisting}
generates the same subgoals but \ssrC{l} has been cleared from both
contexts.

Again applied to the same goal, the command:
\begin{lstlisting}
  move=> l; case: {1 3}l / (lastP l).
\end{lstlisting}
generates the subgoals \ssrL-length l * 2 = length (nil ++ l)- and
\ssrL-forall (s : list A) (x : A), length l * 2 = length (add_last x s++l)-
where the selected occurrences on the left of the \ssrC{/} switch have
been substituted with \ssrC{l} instead of being affected by the case
analysis.

The equation name generation feature combined with a type family \ssrC{/}
  switch generates an equation for the \emph{first} dependent d-item
specified by the user.
Again starting with the above goal, the command:
\begin{lstlisting}
  move=> l; case E: {1 3}l / (lastP l)=>[|s x].
\end{lstlisting}
adds \ssrC{E : l = nil} and \ssrC{E : l = add_last x s},
respectively, to the context of the two subgoals it generates.

There must be at least one \emph{d-item} to the left of the \ssrC{/}
switch; this prevents any
confusion with the view feature. However, the \ditem{}s to the right of
the \ssrC{/} are optional, and if they are omitted the first assumption
provides the instance of the type family.

The equation always refers to the first \emph{d-item} in the actual
tactic call, before any padding with initial $\ssrC{\_}$s. Thus, if an
inductive type has two family parameters, it is possible to have
\ssr{} generate an equation for the second one by omitting the pattern
for the first; note however that this will fail if the type of the
second parameter depends on the value of the first parameter.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Control flow}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Indentation and bullets}\label{ssec:indent}

A linear development of \Coq{} scripts gives little information on
the structure of the proof. In addition, replaying a proof after some
changes in the statement to be proved will usually not display information to
distinguish between the various branches of case analysis for instance.

To help the user in this organization of the proof script at
development time, \ssr{} provides some bullets to highlight the
structure of branching proofs. The available bullets are \ssrC{-},
\ssrC{+} and \ssrC{*}. Combined with tabulation, this lets us highlight four
nested levels of branching; the most we have ever
needed is three. Indeed, the use of ``simpl and closing'' switches, of
terminators (see above section \ref{ssec:termin}) and selectors (see
 section \ref{ssec:select}) is powerful enough
to avoid most of the time more than two levels of indentation.

Here is a fragment of such a structured script:

\begin{lstlisting}
case E1: (abezoutn _ _) => [[| k1] [| k2]].
- rewrite !muln0 !gexpn0 mulg1 => H1.
  move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
  by case/andP; move/eqP.
- rewrite muln0 gexpn0 mulg1 => H1.
  have F1: t %| t * S k2.+1 - 1.
    apply: (@dvdn_trans (orderg x)); first by rewrite F0; exact: dvdn_mull.
    rewrite orderg_dvd; apply/eqP; apply: (mulgI x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P1; case t.
  rewrite dvdn_subr in F1; last by exact: dvdn_mulr.
  + rewrite H1 F0 -{2}(muln1 (p ^ l)); congr (_ * _).
    by apply/eqP; rewrite -dvdn1.
  + by move: P1; case: (t) => [| [| s1]].
- rewrite muln0  gexpn0 mul1g => H1.
...
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Terminators}\label{ssec:termin}
\idx{by \dots{}}

To further structure scripts, \ssr{}
supplies \emph{terminating} tacticals to explicitly close off tactics.
When replaying scripts, we then have the nice property that
an error immediately occurs when a closed tactic fails to prove its
subgoal.

It is hence recommended practice that the proof of any subgoal should
end with a tactic which \emph{fails if it does not solve the current
  goal}, like \ssrC{discriminate}, \ssrC{contradiction} or \ssrC{assumption}.

In fact, \ssr{} provides a generic tactical which turns any tactic into
a closing one (similar to \ssrC{now}). Its general syntax is:

\begin{center}
  \ssrC{by} {\tac}\ssrC{.}
\end{center}

The Ltac expression:

\begin{center}
  \ssrC{by [}\ssrN[1]{tactic} \ssrC{| [}\ssrN[2]{tactic} \ssrC{| ...].}
\end{center}

is equivalent to:

\begin{center}
  \ssrC{[by} \ssrN[1]{tactic} \ssrC{| by} \ssrN[2]{tactic} \ssrC{| ...].}
\end{center}

and this form should be preferred to the former.

In the script provided as example in section \ref{ssec:indent}, the
paragraph corresponding to each sub-case ends with a tactic line prefixed
with a \ssrC{by}, like in:

\begin{center}
  \ssrC{by apply/eqP; rewrite -dvdn1.}
\end{center}


The \ssrC{by} tactical is implemented using the user-defined,
and extensible \ssrC{done} tactic. This \ssrC{done} tactic tries to solve
the current goal by some trivial means and fails if it doesn't succeed.
Indeed, the tactic expression:

\begin{center}
   \ssrC{by} {\tac}\ssrC{.}
\end{center}

is equivalent to:

\begin{center}
  {\tac}\ssrC{; done.}
\end{center}

Conversely, the tactic

\begin{center}
  \ssrC{by [ ].}
\end{center}

is equivalent to:

\begin{center}
  \ssrC{done.}
\end{center}

The default implementation of the \ssrC{done} tactic, in the {\tt
  ssreflect.v} file, is:

\begin{lstlisting}
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].
\end{lstlisting}

The lemma \ssrC{|*not_locked_false_eq_true*|} is needed to discriminate
\emph{locked} boolean predicates (see section \ref{ssec:lock}).
The iterator tactical \ssrC{do} is presented in section
\ref{ssec:iter}.
This tactic can be customized by the user, for instance to include an
\ssrC{auto} tactic.

A natural and common way of closing a goal is to apply a lemma which
is the \ssrC{exact} one needed for the goal to be solved. The defective
form of the tactic:
\begin{lstlisting}
  exact.
\end{lstlisting}
is equivalent to:
\begin{lstlisting}
  do [done | by move=> top; apply top].
\end{lstlisting}
where \ssrC{top} is a fresh name affected to the top assumption of the goal.
This applied form is supported by the  \ssrC{:} discharge tactical, and
the tactic:
\begin{lstlisting}
  exact: MyLemma.
\end{lstlisting}
is equivalent to:
\begin{lstlisting}
  by apply: MyLemma.
\end{lstlisting}
(see section \ref{sss:strongapply} for the documentation of the \ssrC{apply:}
combination).

\textit{Warning} The list of tactics, possibly chained by
semi-columns, that follows a \ssrC{by} keyword is considered as a
parenthesized block
applied to the current goal. Hence for example if the tactic:
\begin{lstlisting}
   by rewrite my_lemma1.
\end{lstlisting}
succeeds, then the tactic:
\begin{lstlisting}
   by rewrite my_lemma1; apply my_lemma2.
\end{lstlisting}
usually fails since it is equivalent to:
\begin{lstlisting}
   by (rewrite my_lemma1; apply my_lemma2).
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Selectors}\label{ssec:select}
\idx{last \dots{} first}
\idx{first \dots{} last}

When composing tactics, the two tacticals \ssrC{first} and
\ssrC{last} let the user restrict the application of a tactic to only one
of the subgoals generated by the previous tactic. This
covers the frequent cases where a tactic generates two subgoals one of
which can be easily disposed of.

This is an other powerful way of linearization of scripts, since it
happens very often that a trivial subgoal can be solved in a less than
one line tactic. For instance, the tactic:

\begin{center}
  \ssrN[1]{tactic}\ssrC{; last by} \ssrN[2]{tactic}\ssrC{.}
\end{center}

tries to solve the last subgoal generated by \ssrN[1]{tactic} using the
\ssrN[2]{tactic}, and fails if it does not succeeds. Its analogous

\begin{center}
  \ssrN[1]{tactic}\ssrC{; first by} \ssrN[2]{tactic}.
\end{center}

tries to solve the first subgoal generated by \ssrN[1]{tactic} using the
tactic \ssrN[2]{tactic}, and fails if it does not succeeds.


\ssr{} also offers an extension of this facility, by supplying
tactics to \emph{permute}  the subgoals generated by a tactic.
The tactic:

\begin{center}
  {\tac}\ssrC{; last first.}
\end{center}

inverts the order of the subgoals generated by {\tac}. It is
equivalent to:

\begin{center}
  {\tac}\ssrC{; first last.}
\end{center}


More generally, the tactic:

\begin{center}
  {\tac}\ssrC{; last }${\naturalnumber}$ \ssrC{first.}
\end{center}

where ${\naturalnumber}$ is
a \Coq{} numeral, or and Ltac variable denoting
a \Coq{} numeral, having the value $k$. It
rotates the $n$ subgoals $G_1,
\dots, G_n$ generated by {\tac}. The first subgoal becomes
$G_{n + 1 - k}$ and the circular order of subgoals remains unchanged.

Conversely, the tactic:

  {\tac}\ssrC{; first }${\naturalnumber}$ \ssrC{last.}

rotates the $n$ subgoals $G_1,
\dots, G_n$ generated by \ssrC{tactic} in order that the first subgoal
becomes $G_{k}$.

Finally, the tactics \ssrC{last} and \ssrC{first} combine with the
branching syntax of Ltac:
if the tactic $\ssrN[0]{tactic}$ generates $n$
subgoals on a given goal, then the tactic

  $tactic_0$\ssrC{; last }${\naturalnumber}$ \ssrC{[}$tactic_1$\ssrC{|}$\dots$\ssrC{|}$tactic_m$\ssrC{] || }$tactic_{m+1}$\ssrC{.}

where ${\naturalnumber}$ denotes the integer $k$ as above, applies $tactic_1$ to the
$n -k + 1$-th goal, $\dots tactic_m$ to the $n -k + 2 - m$-th
goal and $tactic_{m+1}$ to the others.

For instance, the script:
\begin{lstlisting}
  Inductive test : nat ->  Prop :=
    C1 : forall n, test n | C2 : forall n, test n |
    C3 : forall n, test n | C4 : forall n, test n.

  Goal forall n, test n -> True.
  move=> n t; case: t; last 2 [move=> k| move=> l]; idtac.
\end{lstlisting}

creates a goal with four subgoals, the first and the last being
\ssrC{nat -> True}, the second and the third being \ssrC{True} with
respectively \ssrC{k : nat} and \ssrC{l : nat} in their context.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Iteration}\label{ssec:iter}
\idx{do \dots{} [ \dots{} ]}

\ssr{} offers an accurate control on the repetition of
tactics, thanks to the \ssrC{do} tactical, whose general syntax is:

\begin{center}
	\ssrC{do} \optional{\ssrN{mult}} \ssrC{[} \ssrN[1]{tactic} \ssrC{|} $\dots$ \ssrC{|} \ssrN[n]{tactic} \ssrC{]}
\end{center}
where \ssrN{mult} is a \emph{multiplier}.

Brackets can only be omitted if a single tactic is given \emph{and} a
multiplier is present.

A tactic of the form:

\begin{center}
  \ssrC{do [} \tac$_1$ \ssrC{|} $\dots$ \ssrC{|} \tac$_n$\ssrC{].}
\end{center}

is equivalent to the standard Ltac expression:

\begin{center}
  \ssrC{first [} \tac$_1$ \ssrC{|} $\dots$ \ssrC{|} \tac$_n$\ssrC{].}
\end{center}


The optional multiplier \ssrN{mult} specifies how many times
the action of {\tac} should be repeated on the current subgoal.

There are four kinds of multipliers:
  \begin{itemize}
  \item \ssrC{n!}: the step {\tac} is repeated exactly $n$ times
    (where $n$ is a positive integer argument).
  \item \ssrC{!}: the step {\tac} is repeated as many times as possible,
    and done at least once.
  \item \ssrC{?}: the step {\tac} is repeated as many times as possible,
    optionally.
  \item \ssrC{n?}: the step {\tac} is repeated up to $n$ times,
    optionally.
  \end{itemize}

For instance, the tactic:

\begin{center}
 {\tac} \ssrL+; do 1?rewrite mult_comm.+
\end{center}

rewrites at most one time the lemma \ssrC{mult_com} in all the subgoals
generated by {\tac} , whereas the tactic:

\begin{center}
  {\tac} \ssrL+; do 2!rewrite mult_comm.+
\end{center}

rewrites exactly two times the lemma \ssrC{mult_com} in all the subgoals
generated by {\tac}, and fails if this rewrite is not possible
in some subgoal.

Note that the combination of multipliers and \ssrC{rewrite} is so often
used that multipliers are in fact integrated to the syntax of the \ssr{}
\ssrC{rewrite} tactic, see section \ref{sec:rw}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Localization}\label{ssec:gloc}
\idx{\dots{} in \dots{}}

In sections \ref{ssec:loc} and \ref{ssec:profstack}, we have already
presented the \emph{localization} tactical \ssrC{in}, whose general
syntax is:
\begin{center}
	{\tac} \ssrC{in} \ssrN{ident}$^+$ \optional{\ssrC{*}}
\end{center}

where \ssrN{ident}$^+$ is a non empty list of fact
names in the context. On the left side of \ssrC{in}, {\tac} can be
\ssrC{move}, \ssrC{case}, \ssrC{elim}, \ssrC{rewrite}, \ssrC{set},
 or any tactic formed with the general iteration tactical \ssrC{do} (see
 section \ref{ssec:iter}).

The operation described by {\tac} is performed in the facts
listed in \ssrN{ident}$^+$ and in the goal if a \ssrC{*} ends
the list.

The \ssrC{in} tactical successively:
\begin{itemize}
\item generalizes the selected hypotheses, possibly ``protecting'' the
 goal if \ssrC{*} is not present,
\item performs {\tac}, on the obtained goal,
\item reintroduces the generalized facts, under the same names.
\end{itemize}

This defective form of the \ssrC{do} tactical is useful to avoid clashes
between standard Ltac \ssrC{in} and the \ssr{} tactical \ssrC{in}.
For example, in the following script:
\begin{lstlisting}
  Ltac |*mytac*| H := rewrite H.

  Goal forall x y, x = y -> y = 3 -> x + y  = 6.
  move=> x y H1 H2.
  do [mytac H2] in H1 *.
\end{lstlisting}
the last tactic rewrites the hypothesis \ssrC{H2 : y = 3} both in
\ssrC{H1 : x = y} and in the goal \ssrC{x + y = 6}.

By default \ssrC{in} keeps the body of local definitions. To erase
the body of a local definition during the generalization phase,
the name of the local definition must be written between parentheses,
like in \ssrC{rewrite H in H1 (def_n) $\;\;$H2}.

From \ssr{} 1.5 the grammar for the \ssrC{in} tactical has been extended
to the following one:

\begin{center}
  {\tac} \ssrC{in} \optional{ 
	  \ssrN{clear-switch} {\optsep}
	  \optional{\ssrC{@}}\ssrN{ident} {\optsep}
          \ssrC{(}\ssrN{ident}\ssrC{)} {\optsep}
	  \ssrC{(}\optional{\ssrC{@}}\ssrN{ident} \ssrC{:=} \ssrN{c-pattern}\ssrC{)}
		}$^+$ \optional{\ssrC{*}}
\end{center}

In its simplest form the last option lets one rename hypotheses that can't be
cleared (like section variables).  For example \ssrC{(y := x)} generalizes
over \ssrC{x} and reintroduces the generalized
variable under the name \ssrC{y} (and does not clear \ssrC{x}).\\
For a more precise description the $\ssrC{(}[\ssrC{@}]\ssrN{ident}\ \ssrC{:=}\ \ssrN{c-pattern}\ssrC{)}$
item refer to the ``Advanced generalization'' paragraph at page~\pageref{par:advancedgen}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Structure}\label{ssec:struct}

Forward reasoning structures the script by explicitly specifying some
assumptions to be added to the proof context. It is closely associated
with the declarative style of proof, since an extensive use of these
highlighted statements
make the script closer to a (very detailed) text book proof.

Forward chaining tactics allow to state an intermediate lemma and start a
piece of script dedicated to the proof of this statement. The use of
closing tactics (see section \ref{ssec:termin}) and of
indentation makes syntactically explicit the portion of the script
building the proof of the intermediate statement.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{have} tactic.}
\label{sssec:have}
\idx{have: \dots{}}
\idx{have: \dots{} := \dots{}}

The main \ssr{} forward reasoning tactic is the \ssrC{have} tactic. It
can be use in two modes: one starts a new (sub)proof for an
intermediate result in the main proof, and the other
provides explicitly a proof term for this intermediate step.

In the first mode, the syntax of \ssrC{have} in its defective form is:

  \ssrC{have: }{\term}\ssrC{.}

This tactic supports open syntax for {\term}.
Applied to a goal \ssrC{G}, it generates a first subgoal requiring a
proof of {\term} in the context of \ssrC{G}. The  second generated
subgoal is of the form {\term} \ssrC{-> G}, where {\term} becomes
the new top assumption, instead of being introduced with a fresh
name. At the proof-term level, the \ssrC{have} tactic creates a $\beta$
redex, and introduces the lemma under a fresh name, automatically
chosen.


Like in the case of the \ssrC{pose} tactic (see section \ref{ssec:pose}),
the types of the holes are abstracted in {\term}.
For instance, the tactic:
\begin{lstlisting}
  have: _ * 0 = 0.
\end{lstlisting}
is equivalent to:
\begin{lstlisting}
  have: forall n : nat, n * 0 = 0.
\end{lstlisting}
The \ssrC{have} tactic also enjoys the same abstraction mechanism as the
\ssrC{pose} tactic for the non-inferred implicit arguments. For instance,
the tactic:
\begin{lstlisting}
  have: forall x y, (x, y) = (x, y + 0).
\end{lstlisting}
opens a new subgoal to prove that:

\noindent\ssrC{forall (T : Type) (x : T) (y : nat), (x, y) = (x, y + 0)}


The behavior of the defective \ssrC{have} tactic makes it possible to
generalize it in the
following general construction:
\begin{center}
	\ssrC{have} \ssrN{i-item}$^*$ \optional{\ssrN{i-pattern}}
	\optional{\ssrN{s-item} {\optsep} \ssrN{binder}$^+$}
	\optional{\ssrC{:} \ssrN[1]{term}}
	\optional{\ssrC{:=} \ssrN[2]{term} {\optsep} \ssrC{by} {\tac}}
\end{center}

Open syntax is supported for $\ssrN[1]{term}$ and $\ssrN[2]{term}$. For the
description of
\iitem{}s and clear switches see section \ref{ssec:intro}.
The first mode of the \ssrC{have} tactic, which opens a sub-proof for an
intermediate result, uses tactics of the form:

\begin{center}
  \ssrC{have} \ssrN{clear-switch} \ssrN{i-item} \ssrC{:} {\term} \ssrC{by} {\tac}.
\end{center}

which behave like:\\

\begin{center}
  \ssrC{have:} {\term} \ssrC{; first by } {\tac}.
\end{center}
\begin{center}
  \ssrC{  move=>} \ssrN{clear-switch} \ssrN{i-item}.
\end{center}


Note that the \ssrN{clear-switch} \emph{precedes} the
\ssrN{i-item}, which allows to reuse a name of the context, possibly used
by the proof of the assumption, to introduce the new assumption
itself.

The \ssrC{by} feature is especially convenient when the proof script of the
statement is very short, basically when it fits in one line like in:
\begin{lstlisting}
  have H : forall x y, x + y = y + x by move=> x y; rewrite addnC.
\end{lstlisting}

The possibility of using \iitem{}s supplies a very concise
syntax for the further use of the intermediate step. For instance,
\begin{lstlisting}
  have -> : forall x, x * a = a.
\end{lstlisting}
on a goal \ssrC{G}, opens a new subgoal asking for a proof of
\ssrC{forall x, x * a = a}, and a second subgoal in which the lemma
 \ssrC{forall x, x * a = a} has been rewritten in the goal \ssrC{G}. Note
 that in this last subgoal, the intermediate result does not appear in
 the context.
Note that, thanks to the deferred execution of clears, the following
idiom is supported (assuming \ssrC{x} occurs in the goal only):
\begin{lstlisting}
  have {x} -> : x = y
\end{lstlisting}

An other frequent use of the intro patterns combined with \ssrC{have} is the
destruction of existential assumptions like in the tactic:
\begin{lstlisting}
  have [x Px]: exists x : nat, x > 0.
\end{lstlisting}
which opens a new subgoal asking for a proof of \ssrC{exists x : nat, x >
  0} and  a second subgoal in which the witness is introduced under
the name \ssrC{x : nat}, and its property under the name \ssrC{Px : x > 0}.

An alternative use of the \ssrC{have} tactic is to provide the explicit proof
term for the intermediate lemma, using tactics of the form:

\begin{center}
  \ssrC{have} \optional{\ssrN{ident}} \ssrC{:=} {\term}.
\end{center}

This tactic creates a new assumption of type the type of
{\term}. If the
optional \ssrN{ident} is present, this assumption is introduced under
the name \ssrN{ident}. Note that the body of the constant is lost for
the user.

Again, non inferred implicit arguments and explicit holes are abstracted. For
instance, the tactic:
\begin{lstlisting}
  have H := forall x, (x, x) = (x, x).
\end{lstlisting}
adds to the context \ssrC{H : Type -> Prop}. This is a schematic example but
the feature is specially useful when the proof term to give involves
for instance a lemma with some hidden implicit arguments.

After the \ssrN{i-pattern}, a list of binders is allowed.
For example, if \ssrC{Pos_to_P} is a lemma that proves that
\ssrC{P} holds for any positive, the following command:
\begin{lstlisting}
  have H x (y : nat) : 2 * x + y = x + x + y by auto.
\end{lstlisting}
will put in the context \ssrC{H : forall x, 2 * x = x + x}. A proof term
provided after \ssrC{:=} can mention these bound variables (that are
automatically introduced with the given names).
Since the \ssrN{i-pattern} can be omitted, to avoid ambiguity, bound variables
can be surrounded with parentheses even if no type is specified:
\begin{lstlisting}
  have (x) : 2 * x = x + x by auto.
\end{lstlisting}

The \ssrN{i-item}s and \ssrN{s-item} can be used to interpret the
asserted hypothesis with views (see section~\ref{sec:views}) or
simplify the resulting goals.

The \ssrC{have} tactic also supports a \ssrC{suff} modifier which allows for
asserting that a given statement implies the current goal without
copying the goal itself. For example, given a goal \ssrC{G} the tactic
\ssrC{have suff H : P} results in the following two goals:
\begin{lstlisting}
   |- P -> G
   H : P -> G |- G
\end{lstlisting}
Note that \ssrC{H} is introduced in the second goal. The \ssrC{suff}
modifier is not compatible with the presence of a list of binders.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Generating \ssrC{let in} context entries with \ssrC{have}}
\label{sec:havetransparent}

Since \ssr{} 1.5 the \ssrC{have} tactic supports a ``transparent'' modifier to
generate \ssrC{let in} context entries: the \ssrC{@} symbol in front of the context
entry name.  For example:

\begin{lstlisting}
have @i : 'I_n by apply: (Sub m); auto.
\end{lstlisting}
generates the following two context entry:
\begin{lstlisting}
i := Sub m proof_produced_by_auto : 'I_n
\end{lstlisting}

Note that the sub-term produced by \ssrC{auto} is in general huge and
uninteresting, and hence one may want to hide it.

For this purpose the \ssrC{[: name ]} intro pattern and the tactic
\ssrC{abstract} (see page~\pageref{ssec:abstract}) are provided.
Example:
\begin{lstlisting}
have [:blurb] @i : 'I_n by apply: (Sub m); abstract: blurb; auto.
\end{lstlisting}
generates the following two context entries:
\begin{lstlisting}
blurb : (m < n) (*1*)
i := Sub m blurb : 'I_n
\end{lstlisting}
The type of \ssrC{blurb} can be cleaned up by its annotations by just simplifying
it.  The annotations are there for technical reasons only.

When intro patterns for abstract constants are used in conjunction
with \ssrC{have} and an explicit term, they must be used as follows:

\begin{lstlisting}
have [:blurb] @i : 'I_n := Sub m blurb.
  by auto.
\end{lstlisting}

In this case the abstract constant \ssrC{blurb} is assigned by using it
in the term that follows \ssrC{:=} and its corresponding goal is left to
be solved.  Goals corresponding to intro patterns for abstract constants
are opened in the order in which the abstract constants are declared (not
in the ``order'' in which they are used in the term).

Note that abstract constants do respect scopes.  Hence, if a variable
is declared after their introduction, it has to be properly generalized (i.e.
explicitly passed to the abstract constant when one makes use of it).
For example any of the following two lines:
\begin{lstlisting}
have [:blurb] @i k : 'I_(n+k) by apply: (Sub m); abstract: blurb k; auto.
have [:blurb] @i k : 'I_(n+k) := apply: Sub m (blurb k); first by auto.
\end{lstlisting}
generates the following context:
\begin{lstlisting}
blurb : (forall k, m < n+k) (*1*)
i := fun k => Sub m (blurb k) : forall k, 'I_(n+k)
\end{lstlisting}

Last, notice that the use of intro patterns for abstract constants is
orthogonal to the transparent flag \ssrC{@} for \ssrC{have}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{The \ssrC{have} tactic and type classes resolution}
\label{ssec:havetcresolution}

Since \ssr{} 1.5 the \ssrC{have} tactic behaves as follows with respect to type
classes inference.

\begin{itemize}
\item \ssrC{have foo : ty.}
	Full inference for \ssrC{ty}.
	The first subgoal demands a proof of such instantiated statement.
\item \ssrC{have foo : ty := .}
	No inference for \ssrC{ty}. Unresolved instances are quantified in
	\ssrC{ty}.  The first subgoal demands a proof of such quantified
	statement.  Note that no proof term follows \ssrC{:=}, hence two
	subgoals are generated.
\item \ssrC{have foo : ty := t.}
	No inference for \ssrC{ty} and \ssrC{t}.
\item \ssrC{have foo := t.}
	No inference for \ssrC{t}. Unresolved instances are quantified in the
	(inferred) type of \ssrC{t} and abstracted in \ssrC{t}.
\end{itemize}

The behavior of \ssr{} 1.4 and below (never resolve type classes)
can be restored with the option \ssrC{Set SsrHave NoTCResolution}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Variants: the \ssrC{suff} and  \ssrC{wlog} tactics.}
\label{ssec:wlog}
\idx{suff: \dots{}}
\idx{suffices: \dots{}}
\idx{wlog: \dots{} / \dots{}}
\idx{without loss: \dots{} / \dots{}}

As it is often the case  in mathematical textbooks, forward
reasoning may be used in slightly different variants.
One of these variants is to show that the intermediate step $L$
easily implies the initial goal $G$. By easily we mean here that
the proof of $L \Rightarrow G$ is shorter than the one of $L$
itself. This kind of reasoning step usually starts with:
``It suffices to show that \dots''.

This is such a frequent way of reasoning that \ssr{} has a variant of the
\ssrC{have} tactic called \ssrC{suffices} (whose abridged name is
\ssrC{suff}). The \ssrC{have} and \ssrC{suff} tactics are equivalent and
have the same syntax but:
\begin{itemize}
\item the order of the generated subgoals is inversed
\item but the optional clear item is still performed in the
  \emph{second} branch. This means that the tactic:
\begin{lstlisting}
  suff {H} H : forall x : nat, x >= 0.
\end{lstlisting}
fails if the context of the current goal indeed contains an
assumption named \ssrC{H}.
\end{itemize}
The rationale of this clearing policy is to make possible ``trivial''
refinements of an assumption, without changing its name in the main
branch of the reasoning.

The \ssrC{have} modifier can follow the \ssrC{suff} tactic.
For example, given a goal \ssrC{G} the tactic
\ssrC{suff have H : P} results in the following two goals:
\begin{lstlisting}
  H : P |- G
  |- (P -> G) -> G
\end{lstlisting}
Note that, in contrast with \ssrC{have suff}, the name \ssrC{H} has been introduced
in the first goal.

Another useful construct is reduction,
showing that a particular case is in fact general enough to prove
a general property. This kind of reasoning step usually starts with:
``Without loss of generality, we can suppose that \dots''.
Formally, this corresponds to the proof of a goal \ssrC{G} by introducing
a cut \ssrN{wlog\_statement} \ssrC{-> G}. Hence the user shall provide a
proof for both \ssrC{(}\ssrN{wlog\_statement} \ssrC{-> G) -> G} and
\ssrN{wlog\_statement} \ssrC{-> G}. However, such cuts are usually rather
painful to perform by hand, because the statement
\ssrN{wlog\_statement} is tedious to write by hand, and somtimes even
to read.

\ssr{} implements this kind of reasoning step through the \ssrC{without loss}
tactic, whose short name is \ssrC{wlog}. It offers support to describe
the shape of the cut statements, by providing the simplifying
hypothesis and by pointing at the elements of the initial goals which
should be generalized. The general syntax of \ssrC{without loss} is:

\begin{center}
  \ssrC{wlog} \optional{\ssrC{suff}} \optional{\ssrN{clear-switch}} \optional{\ssrN{i-item}} \ssrC{:} \optional{\ssrN[1]{ident} $\dots$ \ssrN[n]{ident}} \ssrC{/} {\term}
\end{center}

where \ssrN[1]{ident} $\dots$ \ssrN[n]{ident} are identifiers for constants
in the context of the goal. Open syntax is supported for {\term}.

In its defective form:

\begin{center}
  \ssrC{wlog: /} {\term}.
\end{center}

on a goal \ssrC{G}, it creates two subgoals: a first one to prove the formula
\ssrC{(}{\term} \ssrC{-> G) -> G} and a second one to prove the formula
{\term} \ssrC{-> G}.

:browse confirm wa
If the optional list \ssrN[1]{ident} $\dots$ \ssrN[n]{ident} is present on the left
side of \ssrC{/}, these constants are generalized in the premise
\ssrC{(}{\term} \ssrC{-> G)} of the first subgoal. By default the body of
local definitions  is erased. This behavior can be inhibited
prefixing the name of the local definition with the \ssrC{@} character.

In the second subgoal, the tactic:

\begin{center}
  \ssrC{move=>} \ssrN{clear-switch}\ssrC{} \ssrN{i-item}\ssrC{.}
\end{center}

is performed if at least one of these optional switches is present in
the \ssrC{wlog} tactic.

The \ssrC{wlog} tactic is specially useful when a symmetry argument
simplifies a proof. Here is an example showing the beginning of the
proof that quotient and reminder of natural number euclidean division
are unique.
\begin{lstlisting}
  Lemma quo_rem_unicity: forall d q1 q2 r1 r2,
     q1*d + r1 = q2*d + r2 -> r1 < d -> r2 < d -> (q1, r1) =  (q2, r2).
  move=> d q1 q2 r1 r2.
  wlog: q1 q2 r1 r2 / q1 <= q2.
    by case (le_gt_dec q1 q2)=> H; last symmetry; eauto with arith.
\end{lstlisting}

The \ssrC{wlog suff} variant is simpler, since it cuts
\ssrN{wlog\_statement} instead of \ssrN{wlog\_statement} \ssrC{-> G}. It thus
opens the goals \ssrN{wlog\_statement} \ssrC{-> G} and \ssrN{wlog\_statement}.

In its simplest form
the \ssrC{generally have :...} tactic
is equivalent to \ssrC{wlog suff :...} followed by \ssrC{last first}.
When the \ssrC{have} tactic
is used with the \ssrC{generally} (or \ssrC{gen}) modifier it accepts an
extra identifier followed by a comma before the usual intro pattern.
The identifier will name the new hypothesis in its more general form,
while the intro pattern will be used to process its instance.  For example:
\begin{lstlisting}
  Lemma simple n (ngt0 : 0 < n ) : P n.
  gen have ltnV, /andP[nge0 neq0] : n ngt0 / (0 <= n) && (n != 0).
\end{lstlisting}
The first subgoal will be
\begin{lstlisting}
  n : nat
  ngt0 : 0 < n
  ====================
  (0 <= n) && (n != 0)
\end{lstlisting}
while the second one will be
\begin{lstlisting}
  n : nat
  ltnV : forall n, 0 < n -> (0 <= n) && (n != 0)
  nge0 : 0 <= n
  neqn0 : n != 0
  ====================
  P n
\end{lstlisting}

\paragraph{Advanced generalization}\label{par:advancedgen}
The complete syntax for the items on the left hand side of the \ssrC{/}
separator is the following one:
\begin{center}
\ssrN{clear-switch} {\optsep} \optional{\ssrC{@}} \ssrN{ident} {\optsep} \ssrC{(}\optional{\ssrC{@}}\ssrN{ident} \ssrC{:=} \ssrN{c-pattern}\ssrC{)}
\end{center}
Clear operations are intertwined with generalization operations. This
helps in particular avoiding dependency issues while generalizing some facts.

\noindent
If an \ssrN{ident} is prefixed with the \ssrC{@} prefix mark, then a
let-in redex is created, which keeps track if its body (if any). The
syntax \ssrC{(}\ssrN{ident}\ssrC{:=}\ssrN{c-pattern}\ssrC{)} allows to
generalize an arbitrary term using a given name.  Note that its simplest
form \ssrC{(x := y)} is just a renaming of \ssrC{y} into \ssrC{x}. In
particular, this can be useful in order to simulate the generalization
of a section variable, otherwise not allowed. Indeed renaming does not
require the original variable to be cleared.


\noindent
The syntax \ssrC{(@x := y)} generates a let-in abstraction but with the following
caveat: \ssrC{x} will not bind \ssrC{y}, but its body, whenever \ssrC{y} can be
unfolded. This cover the case of both local and global definitions, as
illustrated in the following example:

\begin{lstlisting}
Section Test.
Variable x : nat.
Definition addx z := z + x.
Lemma test : x <= addx x.
wlog H : (y := x) (@twoy := addx x) / twoy = 2 * y.
\end{lstlisting}
\noindent
The first subgoal is:
\begin{lstlisting}
   (forall y : nat, let twoy := y + y in twoy = 2 * y -> y <= twoy) ->
   x <= addx x
\end{lstlisting}
\noindent
To avoid unfolding the term captured by the pattern \ssrC{add x} one
can use the pattern \ssrC{id (addx x)}, that would produce the following first
subgoal:
\begin{lstlisting}
   (forall y : nat, let twoy := addx y in twoy = 2 * y -> y <= twoy) ->
   x <= addx x
\end{lstlisting}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Rewriting}\label{sec:rw}
\idx{rewrite \dots{}}

The generalized use of reflection implies that most of the
intermediate results handled are properties of effectively computable
functions. The most efficient mean of establishing such results are
computation and simplification of expressions involving such
functions, i.e., rewriting. \ssr{} therefore includes an extended
\ssrC{rewrite} tactic, that unifies and combines most of the rewriting
functionalities.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{An extended \ssrC{rewrite} tactic}\label{ssec:extrw}
The main features of the \ssrC{rewrite} tactic are:
\begin{itemize}
\item  It can perform an entire series of such operations in any
  subset of the goal and/or context;
\item It allows to perform rewriting,
  simplifications, folding/unfolding of definitions, closing of goals;
\item Several rewriting operations can be chained in a single tactic;
\item Control over the occurrence at which rewriting is to be performed is
  significantly enhanced.
\end{itemize}


The general form of an \ssr{} rewrite tactic is:

\begin{center}
   \ssrC{rewrite} \ssrN{rstep}$^+$\ssrC{.}
\end{center}

The combination of a rewrite tactic with the \ssrC{in} tactical (see
section \ref{ssec:loc}) performs rewriting in both the context and the
goal.

A rewrite step \ssrN{rstep} has the general form:

\begin{center}
  \optional{\ssrN{r-prefix}}\ssrN{r-item}
\end{center}

where:

\begin{longtable}{rcl}
\ssrN{r-prefix} & ::= &
	\optional{\ssrC{-}} \optional{\ssrN{mult}} \optional{\ssrN{occ-switch} {\optsep} \ssrN{clear-switch}} \optional{\ssrC{[}\ssrN{r-pattern}\ssrC{]}}\\
\ssrN{r-pattern} & ::= &
{\term} {\optsep} \ssrC{in} \optional{\ssrN{ident} \ssrC{in}} {\term} {\optsep} \optional{{\term} \ssrC{in} {\optsep} {\term} \ssrC{as} } \ssrN{ident} \ssrC{in} {\term}\\
\ssrN{r-item} & ::= &
\optional{\ssrC{/}}{\term} {\optsep} \ssrN{s-item} \\
\end{longtable}


% \begin{eqnarray*}
% \ssrN{r-prefix} & ::= &
% [\ssrC{-}]\ [\ssrN{mult}][\ssrN{occ-switch} | \ssrN{cl-item}][{\term}]\\
% \ssrN{r-item} & ::= &
% [\ssrC{-}]{\term}\ |\ [\ssrC{-}]\ssrC{[}\ssrN[1]{term}\ssrC{]}\ssrC{/(}\ssrN[2]{term}\ssrC{)} \ |\
% \ssrN{simpl switch} \ |\  \\
% && \ssrN{eq-term} \ |\  \ssrC{(} \ssrN[1]{eq-term}\ssrC{,}\dots
% \ssrC{,}\ssrN[n]{eq-term} \ssrC{)} \ |\  \ssrC{(_ :}\ssrN{eq-term} \ssrC{)}
% \end{eqnarray*}


An \ssrN{r-prefix} contains annotations to qualify where and how   the
rewrite operation should be performed:
\begin{itemize}
\item The optional initial \ssrC{-} indicates the direction of the rewriting
  of \ssrN{r-item}: if present the direction is right-to-left and it is
  left-to-right otherwise.
\item The multiplier \ssrN{mult} (see section \ref{ssec:iter})
  specifies if and how the rewrite operation should be repeated.
\item A rewrite operation matches the occurrences of a \emph{rewrite
  pattern}, and replaces these occurrences by an other term, according
  to the given \ssrN{r-item}.
  The optional \emph{redex switch} $\ssrC{[}\ssrN{r-pattern}\ssrC{]}$, which
  should always be surrounded by brackets, gives explicitly this
  rewrite pattern. In its simplest form, it is a regular term.
  If no explicit redex switch
  is present the rewrite pattern to be matched is inferred from the
  \ssrN{r-item}.
\item This optional {\term}, or
  the \ssrN{r-item}, may be preceded by an
  occurrence switch (see section \ref{ssec:select}) or a clear item
  (see section \ref{ssec:discharge}), these two possibilities being
  exclusive. An occurrence switch selects the occurrences of the
  rewrite pattern which should be affected by the rewrite operation.
\end{itemize}


An \ssrN{r-item} can be:


\begin{itemize}
\item A \emph{simplification r-item}, represented by a
  \ssrN{s-item} (see section \ref{ssec:intro}).
% In some cases, \ssrN{r-prefix}es are not supported.
  Simplification operations are
  intertwined with the possible other rewrite operations specified by
  the list of r-items.
\item A \emph{folding/unfolding r-item}. The tactic:

  \ssrC{rewrite /}{\term}

unfolds the head constant of \textit{term} in every occurrence of the
first matching of \textit{term} in the goal. In particular, if
\ssrC{my_def} is a (local or global) defined constant, the tactic:
\begin{lstlisting}
  rewrite /my_def.
\end{lstlisting}
is analogous to:
\begin{lstlisting}
  unfold my_def.
\end{lstlisting}
Conversely:
\begin{lstlisting}
  rewrite -/my_def.
\end{lstlisting}
is equivalent to:
\begin{lstlisting}
  fold my_def.
\end{lstlisting}
%\emph{Warning} The combination of redex switch with unfold
%\ssrN{r-item} is not yet implemented.

When an unfold r-item is combined with a redex pattern, a conversion
operation is performed. A tactic of the form:

\begin{center}
  \ssrC{rewrite -[}\ssrN[1]{term}\ssrC{]/}\ssrN[2]{term}\ssrC{.}
\end{center}

is equivalent to:


\begin{center}
  \ssrC{change} \ssrN[1]{term} \ssrC{with} \ssrN[2]{term}\ssrC{.}
\end{center}


If \ssrN[2]{term} is a single constant and \ssrN[1]{term} head symbol
is not \ssrN[2]{term}, then the head symbol of \ssrN[1]{term} is
repeatedly unfolded until \ssrN[2]{term} appears.

\begin{lstlisting}
  Definition double x := x + x.
  Definition ddouble x := double (double x).
  Lemma ex1 x : ddouble x = 4 * x.
  rewrite [ddouble _]/double.
\end{lstlisting}

The resulting goal is:

\begin{lstlisting}
  double x + double x = 4 * x
\end{lstlisting}

\emph{Warning} The \ssr{} terms containing holes are \emph{not}
typed as abstractions in this context. Hence the following script:
\begin{lstlisting}
  Definition f := fun x y => x + y.
  Goal forall x y, x +  y = f y x.
  move=> x y.
  rewrite -[f y]/(y + _).
\end{lstlisting}
raises the error message
\begin{verbatim}
   User error: fold pattern (y + _) does not match redex (f y)
\end{verbatim}
but the script obtained by replacing the last line with:
\begin{lstlisting}
  rewrite -[f y x]/(y + _).
\end{lstlisting}
is valid.


\item A term, which can be:
  \begin{itemize}
    \item A term whose type has the form:
      $$\ssrC{forall}\ (x_1\ :\ A_1)\dots(x_n\ :\ A_n),\ eq\ term_1\ term_2$$
      where $eq$ is the Leibniz equality or a registered setoid
      equality. %In the case of setoid relations, the only supported
      %r-prefix is the directional \ssrC{-}.
    \item A list of terms $(t_1,\dots,t_n)$, each $t_i$ having a type of the
      form: $$\ssrC{forall}\ (x_1\ :\ A_1)\dots(x_n\ :\ A_n),\ eq\ term_1\ term_2$$ where
      $eq$ is the Leibniz equality or a registered setoid
      equality. The tactic:

        \centerline{\ssrC{rewrite} \ssrN{r-prefix}\ssrC{(}$t_1$\ssrC{,}$\dots$\ssrC{,}$t_n$\ssrC{).}}

      is equivalent to:

  \centerline{\ssrC{do [rewrite} \ssrN{r-prefix} $t_1$ \ssrC{|} $\dots$ \ssrC| rewrite} \ssrN{r-prefix} $t_n$\ssrC{].}

    \item An anonymous rewrite lemma
      \ssrC{(_ :} {\term}), where \textit{term} has again the form:
      $$\ssrC{forall}\ (x_1\ :\ A_1)\dots(x_n\ :\ A_n),\ eq\ term_1\ term_2$$
      The tactic:

        \centerline{\ssrC{rewrite (_ :} {\term}\ssrC{)}}

      is in fact synonym of:

        \centerline{\ssrC{cutrewrite (}{\term}\ssrC{).}}


  \end{itemize}

\end{itemize}




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Remarks and examples}\label{ssec:rwex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Rewrite redex selection}
The general strategy of \ssr{}
is to grasp as many redexes as possible and to let the user select the
ones to be rewritten thanks to the improved syntax for the control of
rewriting.

This may be a source of incompatibilities between the two \ssrC{rewrite}
tactics.

In a rewrite tactic of the form:

  \ssrC{rewrite} \ssrN{occ-switch}\ssrC{[}\ssrN[1]{term}\ssrC{]}\ssrN[2]{term}.

\ssrN[1]{term} is the explicit rewrite redex and
\ssrN[2]{term} is the
rewrite rule. This execution of this tactic unfolds as follows:

\begin{itemize}
\item First \ssrN[1]{term} and \ssrN[2]{term} are $\beta\iota$ normalized. Then
  \ssrN[2]{term} is put in head normal form if the Leibniz equality
  constructor \ssrC{eq} is not the head symbol. This may involve $\zeta$
  reductions.
\item Then, the matching algorithm (see section \ref{ssec:set})
  determines the first subterm of the goal matching the rewrite pattern.
  The rewrite pattern is
  given by \ssrN[1]{term}, if an explicit redex pattern switch is provided, or by
  the type of \ssrN[2]{term} otherwise. However, matching skips over
  matches that would lead to trivial rewrites. All the
  occurrences of this subterm in the goal are candidates for rewriting.
\item Then only the occurrences coded by \ssrN{occ-switch} (see again
  section \ref{ssec:set}) are finally selected for rewriting.
\item The left hand side of $\ssrN[2]{term}$ is unified with the subterm found
  by the matching algorithm, and if this succeeds, all the selected
  occurrences in the goal are replaced by the right hand side of
  $\ssrN[2]{term}$.
\item Finally the goal is $\beta\iota$ normalized.
\end{itemize}

In the case $\ssrN[2]{term}$ is a list of terms, the first top-down (in
the goal) left-to-right (in the list) matching rule gets selected.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Chained rewrite steps}


The possibility to chain rewrite operations in a single tactic makes
scripts more compact and gathers in a single command line a bunch
of surgical
operations  which would be described by a one sentence in a pen and
paper proof.

Performing rewrite and simplification operations in a single tactic
enhances significantly the concision of scripts. For instance the
tactic:
\begin{lstlisting}
  rewrite /my_def {2}[f _]/= my_eq //=.
\end{lstlisting}
unfolds \ssrC{my_def} in the goal, simplifies the second occurrence of the
first subterm matching pattern \ssrC{[f _]}, rewrites \ssrC{my_eq},
simplifies the whole goal and closes trivial goals.

Here are some concrete examples of chained rewrite operations, in the
proof of basic results on natural numbers arithmetic:

\begin{lstlisting}
  Lemma |*addnS*| : forall m n, m + n.+1 = (m + n).+1.
  Proof. by move=> m n; elim: m. Qed.

  Lemma |*addSnnS*| : forall m n, m.+1 + n = m + n.+1.
  Proof. move=> *; rewrite addnS; apply addSn. Qed.

  Lemma |*addnCA*| : forall m n p, m + (n + p) = n + (m + p).
  Proof. by move=> m n; elim: m => [|m Hrec] p; rewrite ?addSnnS -?addnS. Qed.

  Lemma |*addnC*| : forall m n, m + n = n + m.
  Proof. by move=> m n; rewrite -{1}[n]addn0 addnCA addn0. Qed.
\end{lstlisting}

Note the use of the \ssrC{?} switch for parallel rewrite operations in
the proof of \ssrC{|*addnCA*|}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Explicit redex switches are matched first}
If an \ssrN{r-prefix} involves a \emph{redex switch}, the first step is to
find a subterm matching this redex pattern, independently from the left hand
side \ssrC{t1} of the equality the user wants to rewrite.

For instance, if \ssrL-H : forall t u, t + u = u + t- is in the context of a
goal \ssrL-x + y = y + x-, the tactic:
\begin{lstlisting}
  rewrite [y + _]H.
\end{lstlisting}
transforms the goal into \ssrL-x + y = x + y-.

Note that if this first pattern matching is not compatible with the
\emph{r-item}, the rewrite fails, even if the goal contains a correct
redex matching both the redex switch and the left hand side of the
equality. For instance, if \ssrL-H : forall t u, t + u * 0 = t- is
in the context of a goal \ssrL-x + y * 4 + 2 * 0 = x + 2 * 0-, then tactic:
\begin{lstlisting}
  rewrite [x + _]H.
\end{lstlisting}
raises the error message:
\begin{verbatim}
  User error: rewrite rule H doesn't match redex (x + y * 4)
\end{verbatim}
while the tactic:
\begin{lstlisting}
  rewrite (H _ 2).
\end{lstlisting}
transforms the goal into \ssrL-x + y * 4 = x + 2 * 0-.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Occurrence switches and redex switches}
The tactic:
\begin{lstlisting}
  rewrite {2}[_ + y + 0](_: forall z, z + 0 = z).
\end{lstlisting}
transforms the goal:
\begin{lstlisting}
  x + y + 0 = x + y + y + 0 + 0 + (x + y + 0)
\end{lstlisting}
into:
\begin{lstlisting}
  x + y + 0 = x + y + y + 0 + 0 + (x + y)
\end{lstlisting}
and generates a second subgoal:
\begin{lstlisting}
  forall z : nat, z + 0 = z
\end{lstlisting}
The second subgoal is generated by the use of an anonymous lemma in
the rewrite tactic. The effect of the tactic on the initial goal is to
rewrite this lemma at the second occurrence of the first matching
\ssrL-x + y + 0- of the explicit rewrite redex \ssrL-_ + y + 0-.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Occurrence selection and repetition}
Occurrence selection has priority over repetition switches. This means
the repetition of a rewrite tactic specified by a multiplier
will perform matching each time an elementary rewrite operation is
performed. Repeated rewrite tactics apply to every subgoal generated
by the previous tactic, including the previous instances of the
repetition. For example:
\begin{lstlisting}
  Goal forall x y z : nat,  x + 1 = x + y + 1.
  move=> x y z.
\end{lstlisting}
creates a goal \ssrC{ x + 1 = x + y + 1}, which is turned into \ssrC{z = z}
by the additional tactic:
\begin{lstlisting}
  rewrite 2!(_ : _ + 1 = z).
\end{lstlisting}
In fact, this last tactic generates \emph{three} subgoals,
respectively
\ssrC{ x + y + 1 = z}, \ssrC{ z = z} and \ssrC{x + 1 = z}. Indeed, the second
rewrite operation specified with the \ssrC{2!} multiplier applies to
the two subgoals generated by the first rewrite.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Multi-rule rewriting}
The \ssrC{rewrite} tactic can be provided a \emph{tuple} of rewrite rules,
or more generally a tree of such rules, since this tuple can feature
arbitrary inner parentheses. We call \emph{multirule} such a
generalized rewrite rule. This feature is of special interest when it
is combined with  multiplier switches, which makes the \ssrC{rewrite}
tactic iterates the rewrite operations prescribed by the rules on the
current goal. For instance, let us define two triples \ssrC{multi1} and
\ssrC{multi2} as:
\begin{lstlisting}
  Variables (a b c : nat).

  Hypothesis eqab : a = b.

  Hypothesis eqac : a = c.
\end{lstlisting}

Executing the tactic:
\begin{lstlisting}
  rewrite (eqab, eqac)
\end{lstlisting}
on the goal:
\begin{lstlisting}
  =========
  a = a
\end{lstlisting}
turns it into \ssrC{b = b}, as rule \ssrC{eqab} is the first to apply among
the ones gathered in the tuple passed to the \ssrC{rewrite}
tactic. This multirule \ssrC{(eqab, eqac)} is actually a \Coq{} term and we
can name it with a definition:
\begin{lstlisting}
Definition |*multi1*| := (eqab, eqac).
\end{lstlisting}
In this case, the tactic \ssrC{rewrite multi1} is a synonym for
\ssrC{(eqab, eqac)}. More precisely, a multirule rewrites
the first subterm to which one of the rules applies in a left-to-right
traversal of the goal, with the first rule from the multirule tree in
left-to-right order. Matching is performed according to the algorithm
described in Section~\ref{ssec:set}, but literal matches have
priority. For instance if we add a definition and a new multirule to
our context:

\begin{lstlisting}
  Definition |*d*| := a.

  Hypotheses eqd0 : d = 0.

  Definition |*multi2*| := (eqab, eqd0).
\end{lstlisting}
then executing the tactic:
\begin{lstlisting}
   rewrite multi2.
\end{lstlisting}
on the goal:
\begin{lstlisting}
  =========
  d = b
\end{lstlisting}
turns it into \ssrC{0 = b}, as rule \ssrC{eqd0} applies without unfolding
the definition of \ssrC{d}.  For repeated rewrites the selection process
is repeated anew. For instance, if we define:

\begin{lstlisting}
   Hypothesis eq_adda_b : forall x, x + a = b.

   Hypothesis eq_adda_c : forall x, x + a = c.

   Hypothesis eqb0 : b = 0.

   Definition |*multi3*| := (eq_adda_b, eq_adda_c, eqb0).
\end{lstlisting}
then executing the tactic:
\begin{lstlisting}
  rewrite 2!multi3.
\end{lstlisting}
on the goal:
\begin{lstlisting}
  =========
  1 + a = 12 + a
\end{lstlisting}
turns it into \ssrC{0 = 12 + a}: it uses \ssrC{eq_adda_b} then \ssrC{eqb0} on the
left-hand side only. Now executing the tactic \ssrC{rewrite !multi3}
turns the same goal into \ssrC{0 = 0}.

The grouping of rules inside a multirule does not affect the selection
strategy but can make it easier to include one rule set in another or
to (universally) quantify over the parameters of a subset of rules (as
there is special code that will omit unnecessary quantifiers for rules that
can be syntactically extracted). It is also possible to
reverse the direction of a rule subset, using a special dedicated syntax:
the tactic \ssrC{rewrite (=~ multi1)} is equivalent to
\ssrC{rewrite multi1_rev} with:
\begin{lstlisting}
  Hypothesis eqba : b = a.

  Hypothesis eqca : c = a.

  Definition |*multi1_rev*| := (eqba, eqca).
\end{lstlisting}
except that the constants \ssrC{eqba, eqab, mult1_rev} have not been created.

Rewriting with multirules is useful to implement simplification or
transformation procedures, to be applied on terms of small to medium
size. For instance, the library \ssrL{ssrnat} --- available in the
external math-comp library --- provides two implementations for
arithmetic operations on natural numbers: an elementary one and a tail
recursive version, less inefficient but also less convenient for
reasoning purposes. The library also provides one lemma per such
operation, stating that both versions return the same values when
applied to the same arguments:

\begin{lstlisting}
  Lemma |*addE*| : add =2 addn.
  Lemma |*doubleE*| : double =1 doublen.
  Lemma |*add_mulE*| n m s : add_mul n m s = addn (muln n m) s.
  Lemma |*mulE*| : mul =2 muln.
  Lemma |*mul_expE*| m n p : mul_exp m n p = muln (expn m n) p.
  Lemma |*expE*| : exp =2 expn.
  Lemma |*oddE*| : odd =1 oddn.
\end{lstlisting}

The operation on the left hand side of each lemma is the efficient
version, and the corresponding naive implementation is on the right
hand side. In order to reason conveniently on expressions involving
the efficient operations, we gather all these rules in the
definition \ssrC{|*trecE*|}:
\begin{lstlisting}
 Definition |*trecE*| := (addE, (doubleE, oddE), (mulE, add_mulE, (expE, mul_expE))).
\end{lstlisting}
The tactic:
\begin{lstlisting}
  rewrite !trecE.
\end{lstlisting}
restores the naive versions of each operation in a goal involving the
efficient ones, e.g. for the purpose of a correctness proof.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Wildcards vs abstractions}
     The \ssrC{rewrite} tactic supports r-items containing holes. For example
      in the tactic $(1)$:
\begin{lstlisting}
  rewrite (_ : _ * 0 = 0).
\end{lstlisting}
      the term \ssrC{_ * 0 = 0} is interpreted as \ssrC{forall n : nat, n * 0 = 0}.
      Anyway this tactic is \emph{not} equivalent to the tactic $(2)$:
\begin{lstlisting}
  rewrite (_ : forall x, x * 0 = 0).
\end{lstlisting}
      The tactic $(1)$ transforms the goal
      \ssrL-(y * 0) + y * (z * 0) = 0- into \ssrC{y * (z * 0) = 0}
      and generates a new subgoal to prove the statement \ssrC{y * 0 = 0},
      which is the \emph{instance} of the\\ \ssrC{forall x, x * 0 = 0}
      rewrite rule that
      has been used to perform the rewriting. On the other hand, tactic
      $(2)$ performs the same rewriting on the current goal but generates a
      subgoal to prove \ssrC{forall x, x * 0 = 0}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{When \ssr{} \ssrC{rewrite} fails on standard \Coq{} licit rewrite}
In a few cases, the \ssr{} \ssrC{rewrite} tactic fails
rewriting some redexes which standard \Coq{} successfully rewrites.
There are two main cases:

\begin{itemize}
\item \ssr{} never accepts to rewrite indeterminate patterns like:
\begin{lstlisting}
  Lemma |*foo*| : forall x : unit, x = tt.
\end{lstlisting}
\ssr{} will however accept the $\eta\zeta$ expansion of this rule:
\begin{lstlisting}
  Lemma |*fubar*| : forall x : unit, (let u := x in u) = tt.
\end{lstlisting}
\item In standard \Coq{}, suppose that we work in the following context:
\begin{lstlisting}
  Variable g : nat -> nat.
  Definition |*f*| := g.
\end{lstlisting}
then rewriting \ssrC{H : forall x, f x = 0} in the goal
\ssrC{g 3 + g 3 = g 6} succeeds
and transforms the goal into \ssrC{0 + 0 = g 6}.

This rewriting is not possible in \ssr{} because there is no
occurrence of the head symbol \ssrC{f} of the rewrite rule in the
goal. Rewriting with \ssrC{H} first requires unfolding the occurrences of
\ssrC{f} where the substitution is to be performed (here there is a single
such occurrence), using tactic \ssrC{rewrite /f} (for a global
replacement of \ssrC{f} by \ssrC{g}) or \ssrC{rewrite $\ \ssrN{pattern}$/f}, for a
finer selection.
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Existential metavariables and rewriting}
\label{ssec:rewcaveats}
The \ssrC{rewrite} tactic will not instantiate existing existential
metavariables when matching a redex pattern.

If a rewrite rule generates a goal
with new existential metavariables, these will be generalized as for \ssrC{apply}
(see page~\pageref{sssec:apply}) and corresponding new goals will be generated.
For example, consider the following script:

\begin{lstlisting}
  Lemma |*ex3*| (x : 'I_2) y (le_1 : y < 1) (E : val x = y) : Some x = insub y.
  rewrite insubT ?(leq_trans le_1)// => le_2.
\end{lstlisting}

Since \ssrC{insubT} has the following type:

\begin{lstlisting}
  forall T P (sT : subType P) (x : T) (Px : P x), insub x = Some (Sub x Px)
\end{lstlisting}

and since the implicit argument corresponding to the \ssrC{Px} abstraction is not
supplied by the user, the resulting goal should be \ssrC{Some x = Some (Sub y
$\;\;?_{Px}$)}. Instead, \ssr{} \ssrC{rewrite} tactic generates the two following
goals:
\begin{lstlisting}
  y < 2
  forall Hyp0 : y < 2, Some x = Some (Sub y Hyp0)
\end{lstlisting}
The script closes the former with \ssrC{?(leq_trans le_1)//}, then it introduces
the new generalization naming it \ssrC{le_2}.

\begin{lstlisting}
  x : 'I_2
  y : nat
  le_1 : y < 1
  E : val x = y
  le_2 : y < 2
  ============================
   Some x = Some (Sub y le_2)
\end{lstlisting}

As a temporary limitation, this behavior is available only if the rewriting
rule is stated using Leibniz equality (as opposed to setoid relations).
It will be extended to other rewriting relations in the future.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Locking, unlocking} \label{ssec:lock}

As program proofs tend to generate large goals, it is important to be
able to control the partial evaluation performed by the simplification
operations that are performed by the tactics. These evaluations can
for example come from a \ssrC{/=} simplification switch, or from rewrite steps
which may expand large terms while performing conversion. We definitely
want to avoid repeating large subterms of the goal in
the proof script. We do this by
``clamping down'' selected function symbols in the goal, which
prevents them from
being considered in simplification or rewriting steps. This clamping
is accomplished by using the occurrence switches (see section
\ref{sssec:occselect}) together with ``term tagging'' operations.

\ssr{} provides two levels of tagging.

The first one uses auxiliary definitions to introduce a provably equal
copy of any term \ssrC{t}. However this copy is (on purpose)
\emph{not convertible} to \ssrC{t} in the \Coq{} system\footnote{This is
  an implementation feature: there is not such obstruction in the
  metatheory}. The job is done by the following construction:

\begin{lstlisting}
  Lemma |*master_key*| : unit. Proof. exact tt. Qed.
  Definition |*locked*| A := let: tt := master_key in fun x : A => x.
  Lemma |*lock*| : forall A x, x = locked x :> A.
\end{lstlisting}
Note that the definition of \ssrC{|*master_key*|} is explicitly opaque.
The equation \ssrC{t = locked t} given by the \ssrC{lock} lemma can be used
for selective rewriting, blocking on the fly the reduction in the
term \ssrC{t}.
For example the script:
\begin{lstlisting}
  Require Import List.
  Variable A : Type.

  Fixpoint |*my_has*| (p : A -> bool)(l : list A){struct l} : bool:=
    match l with
      |nil => false
      |cons x l => p x || (my_has p l)
    end.

  Goal forall a x y l, a x = true -> my_has a ( x :: y :: l) = true.
  move=> a x y l Hax.
\end{lstlisting}
where \ssrL{||} denotes the boolean disjunction, results in a goal
\ssrC{my_has a ( x :: y :: l) = true}. The tactic:
\begin{lstlisting}
  rewrite {2}[cons]lock /= -lock.
\end{lstlisting}
turns it into \ssrC{a x || my_has a (y :: l) = true}.
Let us now start by reducing the initial goal without blocking reduction.
The script:
\begin{lstlisting}
  Goal forall a x y l, a x = true -> my_has a ( x :: y :: l) = true.
  move=> a x y l Hax /=.
\end{lstlisting}
creates a goal \ssrC{(a x) || (a y) || (my_has a l) = true}. Now the
tactic:
\begin{lstlisting}
  rewrite {1}[orb]lock orbC -lock.
\end{lstlisting}
where \ssrC{orbC} states the commutativity of \ssrC{orb}, changes the
goal into\\ \ssrC{(a x) || (my_has a l) || (a y) = true}: only the
arguments of the second disjunction where permuted.


It is sometimes desirable to globally prevent a definition from being
expanded by simplification; this is done by adding \ssrC{locked} in the
definition.

For instance, the function \ssrC{|*fgraph_of_fun*|} maps a function whose
domain and codomain are finite types to a concrete representation of
its (finite) graph. Whatever implementation of this transformation we
may use, we want it to be hidden to simplifications and tactics, to
avoid the collapse of the graph object:
\begin{lstlisting}
  Definition |*fgraph_of_fun*| :=
    locked
    (fun (d1 :finType) (d2 :eqType) (f : d1 -> d2) => Fgraph (size_maps f _)).
\end{lstlisting}

We provide a special tactic \ssrC{unlock} for unfolding such definitions
while removing ``locks'', e.g., the tactic:

  \ssrC{unlock} \ssrN{occ-switch}\ssrC{fgraph_of_fun}.

replaces the occurrence(s) of \ssrC{fgraph_of_fun} coded by the \ssrN{occ-switch}
with \ssrC{(Fgraph (size_maps _ _))} in the goal.

We found that it was usually preferable to prevent the expansion of
some functions by the partial evaluation switch ``/='', unless
this allowed the evaluation of a condition. This is possible thanks to
an other mechanism of term tagging, resting on the following
\emph{Notation}:
\begin{lstlisting}
  Notation "'nosimpl' t" := (let: tt := tt in t).
\end{lstlisting}

The term \ssrC{(nosimpl t)} simplifies to t \emph{except} in a
definition. More precisely,
given:
\begin{lstlisting}
  Definition |*foo*| := (nosimpl bar).
\end{lstlisting}
the term \ssrC{foo (or (foo t'))} will \emph{not} be expanded by the
\emph{simpl} tactic unless it is in a forcing context (e.g., in
\ssrC{match foo t' with $\dots$ end}, \ssrC{foo t'} will be reduced if this allows
\ssrC{match} to be reduced). Note that \ssrC{nosimpl bar} is simply notation
for a term that reduces to \ssrC{bar}; hence \ssrC{unfold foo} will replace
    \ssrC{foo} by \ssrC{bar}, and \ssrC{fold foo} will replace \ssrC{bar} by
    \ssrC{foo}.

\emph{Warning} The \ssrC{nosimpl} trick only works if no reduction is
apparent in \ssrC{t}; in particular, the declaration:
\begin{lstlisting}
  Definition |*foo*| x := nosimpl (bar x).
\end{lstlisting}
will usually not work. Anyway, the common practice is to tag only the
function, and to use the following definition, which blocks the
reduction as expected:
\begin{lstlisting}
  Definition |*foo*| x := nosimpl bar x.
\end{lstlisting}


A standard example making this technique shine is the case of
arithmetic operations. We define for instance:
\begin{lstlisting}
  Definition |*addn*| := nosimpl plus.
\end{lstlisting}
The operation \ssrC{addn} behaves exactly like plus, except that
\ssrC{(addn (S n) m)} will not
simplify spontaneously to \ssrC{(S (addn n m))} (the two terms, however, are
inter-convertible). In addition, the unfolding step:
\begin{lstlisting}
rewrite /addn
\end{lstlisting}
will replace \ssrC{addn} directly with \ssrC{plus}, so the \ssrC{nosimpl} form
is essentially invisible.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Congruence}\label{ssec:congr}

Because of the way matching interferes with type families parameters,
the tactic:
\begin{lstlisting}
  apply: my_congr_property.
\end{lstlisting}
will generally fail to perform congruence simplification, even on
rather simple cases. We therefore provide a
more robust alternative in which the function is supplied:
$$\ssrC{congr}\ [\ssrN{int}]\ {\term}$$

This tactic:
\begin{itemize}
\item checks that the goal is a Leibniz equality
\item matches both sides of this equality with ``{\term} applied to
  some arguments'', inferring the right number of arguments from the goal
  and the type of {\term}. This may
  expand some definitions or fixpoints.
\item generates the subgoals corresponding to pairwise equalities of
  the arguments present in the goal.
\end{itemize}

The goal can be a non dependent product \ssrC{P -> Q}.
In that case, the system asserts the equation \ssrC{P = Q}, uses it to solve
the goal, and calls the \ssrC{congr} tactic on the remaining goal
\ssrC{P = Q}. This can be useful for instance to perform a transitivity
step, like in the following situation:
\begin{lstlisting}
  x, y, z : nat
  ===============
  x = y -> x = z
\end{lstlisting}
the tactic \ssrC{congr (_ = _)} turns this goal into:

\begin{lstlisting}
  x, y, z : nat
  ===============
  y = z
\end{lstlisting}
which can also be obtained starting from:
\begin{lstlisting}
  x, y, z : nat
  h : x = y
  ===============
  x = z
\end{lstlisting}
and using the tactic \ssrC{congr (_ = _): h}.

The optional \ssrN{int} forces the number of arguments for which the
tactic should generate equality proof obligations.

This tactic supports equalities between applications with dependent
arguments. Yet dependent arguments should have exactly the same
parameters on both sides, and these parameters should appear as first
arguments.

The following script:
\begin{lstlisting}
  Definition f n := match n with 0 => plus | S _ => mult end.
  Definition g (n m : nat) := plus.

  Goal forall x y, f 0 x y = g 1 1 x y.
  by move=> x y; congr plus.
  Qed.
\end{lstlisting}
shows that the \ssrC{congr} tactic matches \ssrC{plus} with \ssrC{f 0} on the
left hand side and \ssrC{g 1 1} on the right hand side, and solves the goal.

The script:
\begin{lstlisting}
  Goal forall n m, m <= n -> S m + (S n - S m) = S n.
  move=> n m Hnm; congr S; rewrite -/plus.
\end{lstlisting}
generates the subgoal \ssrC{m + (S n - S m) = n}. The tactic
\ssrC{rewrite -/plus} folds back the expansion of \ssrC{plus} which was
necessary for matching both sides of the equality with an application
of \ssrC{S}.

Like most \ssr{} arguments, {\term} can contain wildcards.
The script:
\begin{lstlisting}
  Goal forall x y, x + (y * (y + x - x)) = x * 1 + (y + 0) * y.
  move=> x y; congr ( _ + (_ * _)).
\end{lstlisting}
generates three subgoals, respectively \ssrC{x = x * 1}, \ssrC{y = y + 0}
and \ssrC{ y + x - x = y}.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Contextual patterns}
\label{ssec:rewp}

The simple form of patterns used so far, ${\term}s$ possibly containing
wild cards, often require an additional \ssrN{occ-switch} to be specified.
While this may work pretty fine for small goals, the use of polymorphic
functions and dependent types may lead to an invisible duplication of functions
arguments. These copies usually end up in types hidden by the implicit
arguments machinery or by user defined notations.  In these situations
computing the right occurrence numbers is very tedious because they must be
counted on the goal as printed after setting the \ssrC{Printing All} flag.
Moreover the resulting script is not really informative for the reader, since
it refers to occurrence numbers he cannot easily see.

Contextual patterns mitigate these issues allowing to specify occurrences
according to the context they occur in.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Syntax}

The following table summarizes the full syntax of
\ssrN{c-pattern} and the corresponding subterm(s) identified
by the pattern.
In the third column we use s.m.r. for
``the subterms matching the redex'' specified in the second column.

\begin{center}
%\begin{tabularx}{\textwidth}{>{\arraybackslash}m{0.30\textwidth}|>{\arraybackslash}m{0.21\textwidth}|>{\arraybackslash}m{0.39\textwidth}}
\begin{tabular}{llp{10em}}
\ssrN{c-pattern} & redex & subterms affected \\
\hline
{\term} & {\term} & all occurrences of {\term}\\
\hline
$\ssrN{ident}\ \ssrC{in}\ {\term}$ &
  subterm of {\term} selected by \ssrN{ident} &
  all the subterms identified by \ssrN{ident} in all
  the occurrences of {\term} \\
\hline
$\ssrN[1]{term}\ \ssrC{in}\ \ssrN{ident}\ \ssrC{in}\ \ssrN[2]{term}$ & $\ssrN[1]{term}$ &
  in all  s.m.r. in all the subterms identified by \ssrN{ident} in all
  the occurrences of $\ssrN[2]{term}$ \\
\hline
$\ssrN[1]{term}\ \ssrC{as}\ \ssrN{ident}\ \ssrC{in}\ \ssrN[2]{term}$ & $\ssrN[1]{term}$ &
  in all the subterms identified by \ssrN{ident} in all
  the occurrences of $\ssrN[2]{term}[\ssrN[1]{term}/\ssrN{ident}]$\\
\hline
%\end{tabularx}
\end{tabular}
\end{center}

The \ssrC{rewrite} tactic supports two more patterns obtained
prefixing the first two with \ssrC{in}. The intended meaning is that the
pattern identifies all subterms of the specified context. The
\ssrC{rewrite} tactic will infer a pattern for the redex looking at the
rule used for rewriting.

\begin{center}
\begin{tabularx}{\textwidth}{>{\arraybackslash}m{0.30\textwidth}|>{\arraybackslash}m{0.21\textwidth}|>{\arraybackslash}m{0.39\textwidth}}
\ssrN{r-pattern} & redex & subterms affected \\
\hline
$\ssrC{in}\ {\term}$ & inferred from rule &
  in all  s.m.r. in all occurrences of {\term}\\
\hline
$\ssrC{in}\ \ssrN{ident}\ \ssrC{in}\ {\term}$ & inferred from rule &
  in all  s.m.r. in all the subterms identified by \ssrN{ident} in all
  the occurrences of {\term} \\
\hline
\end{tabularx}
\end{center}

The first \ssrN{c-pattern} is the simplest form matching any
context but selecting a specific redex and has been described in the
previous sections. We have seen so far that the possibility of
selecting a redex using a term with holes is already a powerful mean of redex
selection. Similarly, any {\term}s provided by the
user in the more complex forms of \ssrN{c-pattern}s presented in the
tables above can contain holes.

For a quick glance at what can be expressed with the last
\ssrN{r-pattern} consider the goal \ssrC{a = b} and the tactic
\begin{lstlisting}
  rewrite [in X in _ = X]rule.
\end{lstlisting}
It rewrites all occurrences of the left hand side of \ssrC{rule} inside
\ssrC{b} only (\ssrC{a}, and the hidden type of the equality, are ignored).
Note that the variant \ssrC{rewrite [X in _ = X]rule} would have
rewritten \ssrC{b} exactly (i.e., it would only work if \ssrC{b} and the
left hand side of \ssrC{rule} can be unified).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Matching contextual patterns}

The \ssrN{c-pattern}s and \ssrN{r-pattern}s involving
{\term}s with holes are matched
against the goal in order to find a closed instantiation. This
matching proceeds as follows:

\begin{center}
\begin{tabularx}{\textwidth}{>{\arraybackslash}m{0.30\textwidth}|>{\arraybackslash}m{0.65\textwidth}}
\ssrN{c-pattern} & instantiation order and place for $\ssrN[i]{term}$ and redex\\
\hline
{\term} & {\term} is matched against the goal, redex is unified with
    the instantiation of {\term}\\
\hline
$\ssrN{ident}\ \ssrC{in}\ {\term}$ &
    {\term} is matched against the goal, redex is
    unified with the subterm of the
    instantiation of {\term} identified by \ssrN{ident}\\
\hline
$\ssrN[1]{term}\ \ssrC{in}\ \ssrN{ident}\ \ssrC{in}\ \ssrN[2]{term}$ &
    $\ssrN[2]{term}$ is matched against the goal, $\ssrN[1]{term}$ is
    matched against the subterm of the
    instantiation of $\ssrN[1]{term}$ identified by \ssrN{ident},
    redex is unified with the instantiation of $\ssrN[1]{term}$\\
\hline
$\ssrN[1]{term}\ \ssrC{as}\ \ssrN{ident}\ \ssrC{in}\ \ssrN[2]{term}$ &
    $\ssrN[2]{term}[\ssrN[1]{term}/\ssrN{ident}]$
    is matched against the goal,
    redex is unified with the instantiation of $\ssrN[1]{term}$\\
\hline
\end{tabularx}
\end{center}

In the following patterns, the redex is intended to be inferred from the
rewrite rule.

\begin{center}
\begin{tabularx}{\textwidth}{>{\arraybackslash}m{0.30\textwidth}|>{\arraybackslash}m{0.65\textwidth}}
\ssrN{r-pattern} & instantiation order and place for $\ssrN[i]{term}$ and redex\\
\hline
$\ssrC{in}\ \ssrN{ident}\ \ssrC{in}\ {\term}$ &
    {\term} is matched against the goal, the redex is
    matched against the subterm of the
    instantiation of {\term} identified by \ssrN{ident}\\
\hline
$\ssrC{in}\ {\term}$ & {\term} is matched against the goal, redex is
   matched against the instantiation of {\term}\\
\hline
\end{tabularx}
\end{center}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Examples}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection{Contextual pattern in \ssrC{set} and the \ssrC{:} tactical}

As already mentioned in section~\ref{ssec:set} the \ssrC{set} tactic
takes as an argument a term in open syntax. This term is interpreted
as the simplest for of \ssrN{c-pattern}. To void confusion in the grammar,
open syntax is supported only for the simplest form of patterns, while
 parentheses are required around more complex patterns.

\begin{lstlisting}
set t := (X in _ = X).
set t := (a + _ in X in _ = X).
\end{lstlisting}

Given the goal \ssrC{a + b + 1 = b + (a + 1)} the first tactic
captures \ssrC{b + (a + 1)}, while the latter \ssrC{a + 1}.

Since the user may define an infix notation for \ssrC{in} the former
tactic may result ambiguous. The disambiguation rule implemented is
to prefer patterns over simple terms, but to interpret a pattern with
double parentheses as a simple term. For example
the following tactic would capture any occurrence of the term `\ssrC{a in A}'.

\begin{lstlisting}
set t := ((a in A)).
\end{lstlisting}

Contextual pattern can also be used as arguments of the \ssrC{:} tactical.
For example:
\begin{lstlisting}
elim: n (n in _ = n) (refl_equal n).
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection{Contextual patterns in \ssrC{rewrite}}
As a more comprehensive example consider the following goal:
\begin{lstlisting}
    (x.+1 + y) + f (x.+1 + y) (z + (x + y).+1) = 0
\end{lstlisting}
The tactic \ssrC{rewrite [in f _ _]addSn} turns it into:
\begin{lstlisting}
    (x.+1 + y) + f (x + y).+1 (z + (x + y).+1) = 0
\end{lstlisting}
since the simplification rule \ssrC{addSn} is applied only under the \ssrC{f} symbol.
Then we simplify also the first addition and expand \ssrC{0} into \ssrC{0+0}.
\begin{lstlisting}
    rewrite addSn -[X in _ = X]addn0.
\end{lstlisting}
obtaining:
\begin{lstlisting}
    (x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 + 0
\end{lstlisting}
Note that the right hand side of \ssrC{addn0} is undetermined, but the
rewrite pattern specifies the redex explicitly. The right hand side of
\ssrC{addn0} is unified with the term identified by \ssrC{X}, \ssrC{0} here.

The following pattern does not specify a redex, since it
identifies an entire region, hence the rewrite rule has to be instantiated
explicitly. Thus the tactic:
\begin{lstlisting}
    rewrite -{2}[in X in _ = X](addn0 0).
\end{lstlisting}
changes the goal as follows:
\begin{lstlisting}
    (x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 + (0 + 0)
\end{lstlisting}
The following tactic is quite tricky:
\begin{lstlisting}
    rewrite [_.+1 in X in f _ X](addnC x.+1).
\end{lstlisting}
and the resulting goals is:
\begin{lstlisting}
    (x + y).+1 + f (x + y).+1 (z + (y + x.+1)) = 0 + (0 + 0)
\end{lstlisting}
The explicit redex \ssrC{_.+1} is important since its head
constant \ssrC{S} differs from the head constant inferred from
\ssrC{(addnC x.+1)} (that is \ssrC{addn}, denoted \ssrC{+} here).
Moreover, the pattern \ssrC{f _ X} is important to rule out the first occurrence
of \ssrC{(x + y).+1}. Last, only the subterms of \ssrC{f _ X} identified by \ssrC{X} are
rewritten, thus the first argument of \ssrC{f} is skipped too.
Also note the pattern \ssrC{_.+1} is interpreted in the context
identified by \ssrC{X}, thus it gets instantiated to \ssrC{(y + x).+1} and
not \ssrC{(x + y).+1}.

The last rewrite pattern allows to specify exactly the shape of the term
identified by \ssrC{X}, that is thus unified with the left hand side of the
rewrite rule.
\begin{lstlisting}
    rewrite [x.+1 + y as X in f X _]addnC.
\end{lstlisting}
The resulting goal is:
\begin{lstlisting}
    (x + y).+1 + f (y + x.+1) (z + (y + x.+1)) = 0 + (0 + 0)
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Patterns for recurrent contexts}

The user can define shortcuts for recurrent contexts corresponding to the
\ssrN{ident} \ssrC{in} {\term} part. The notation scope identified
with \ssrC{\%pattern} provides a special notation `\ssrC{(X in t)}' the user
must adopt to define context shortcuts.

The following example is taken from \ssrC{ssreflect.v} where the
\ssrC{LHS} and \ssrC{RHS} shortcuts are defined.

\begin{lstlisting}
Notation RHS := (X in _ = X)%pattern.
Notation LHS := (X in X = _)%pattern.
\end{lstlisting}

Shortcuts defined this way can be freely used in place of the
trailing \ssrN{ident} \ssrC{in} {\term} part of any contextual
pattern.
Some examples follow:

\begin{lstlisting}
set rhs := RHS.
rewrite [in RHS]rule.
case: (a + _ in RHS).
\end{lstlisting}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Views and reflection}\label{sec:views}

The bookkeeping facilities presented in section \ref{sec:book} are
crafted to ease simultaneous introductions and generalizations of facts and
casing,
naming $\dots$ operations. It also a common practice to make a stack
operation immediately followed by an \emph{interpretation} of the fact
being pushed,
that is, to apply a lemma to this fact before passing it
to a tactic for decomposition, application and so on.


% possibly

% Small scale reflection consists in using a two levels
% approach locally when developing formal proofs. This means that a
% fact, which may be an assumption, or the goal itself, will often be
% \emph{interpreted} before being passed to a tactic
% for decomposition, application and so on.

\ssr{} provides a convenient, unified syntax to combine these
interpretation operations with the proof stack operations. This
\emph{view mechanism} relies on the combination of the \ssrC{/} view
switch with bookkeeping tactics and tacticals.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Interpreting eliminations}
\idx{elim/\dots{}}

The view syntax combined with the \ssrC{elim} tactic specifies an
elimination scheme to
be used instead of the default, generated, one. Hence the \ssr{} tactic:
\begin{lstlisting}
  elim/V.
\end{lstlisting}
is a synonym for:
\begin{lstlisting}
  intro top; elim top using V; clear top.
\end{lstlisting}
where \ssrC{top} is a fresh name and \ssrC{V} any second-order lemma.

Since an elimination view supports the two bookkeeping tacticals of
discharge and introduction (see section \ref{sec:book}), the \ssr{} tactic:
\begin{lstlisting}
  elim/V: x => y.
\end{lstlisting}
is a synonym for:
\begin{lstlisting}
  elim x using V; clear x; intro y.
\end{lstlisting}
where \ssrC{x} is a variable in the context, \ssrC{y} a fresh name and \ssrC{V}
any second order lemma; \ssr{} relaxes the syntactic restrictions of
the \Coq{} \ssrC{elim}. The first pattern following \ssrC{:} can be a \ssrC{_}
wildcard if the conclusion of the view \ssrC{V} specifies a pattern for
its last argument (e.g., if \ssrC{V} is a functional induction lemma
generated by the \ssrC{Function} command).

The elimination view mechanism is compatible with the equation name
generation (see section \ref{ssec:equations}).

The following script illustrate a toy example of this feature. Let us
define a function adding an element at the end of a list:
\begin{lstlisting}
  Require Import List.

  Variable d : Type.

  Fixpoint |*add_last*|(s : list d) (z : d) {struct s} : list d :=
    match s with
    | nil =>  z :: nil
    | cons x s' => cons x (add_last s' z)
    end.
\end{lstlisting}

One can define an alternative, reversed, induction principle on inductively
defined \ssrC{list}s, by proving the following lemma:

\begin{lstlisting}
  Lemma |*last_ind_list*| : forall (P : list d -> Type),
  P nil ->
  (forall (s : list d) (x : d), P s -> P (add_last s x)) -> forall s : list d, P s.
\end{lstlisting}

Then the combination of elimination views with equation names result
in a concise syntax for reasoning inductively using the user
defined elimination scheme. The script:
\begin{lstlisting}
  Goal forall (x : d)(l : list d), l = l.
  move=> x l.
  elim/last_ind_list E : l=> [| u v]; last first.
\end{lstlisting}
generates two subgoals: the first one to prove \ssrC{nil = nil} in a
context featuring \ssrC{E : l = nil} and the second to prove
\ssrC{add_last u v = add_last u v}, in a context containing
\ssrC{E : l = add_last u v}.

User provided eliminators (potentially generated with the
\ssrC{Function} \Coq{}'s command) can be combined with the type family switches
described in section~\ref{ssec:typefam}. Consider an eliminator
\ssrC{foo_ind} of type:

  \ssrC{foo_ind : forall $\dots$, forall x : T, P p$_1$ $\dots$ p$_m$}

and consider the tactic

  \ssrC{elim/foo_ind: e$_1$ $\dots$ / e$_n$}

The \ssrC{elim/} tactic distinguishes two cases:
\begin{description}
\item[truncated eliminator] when \ssrC{x} does not occur in \ssrC{P p$_1 \dots$ p$_m$}
  and the type of \ssrC{e$_n$} unifies with \ssrC{T} and \ssrC{e$_n$} is not \ssrC{_}.
  In that case, \ssrC{e$_n$} is passed to the eliminator as the last argument
  (\ssrC{x} in \ssrC{foo_ind}) and \ssrC{e$_{n-1} \dots$ e$_1$} are used as patterns
  to select in the goal the occurrences that will be bound by the
  predicate \ssrC{P}, thus it must be possible to unify the sub-term of
  the goal matched by \ssrC{e$_{n-1}$} with \ssrC{p$_m$}, the one matched by
  \ssrC{e$_{n-2}$} with \ssrC{p$_{m-1}$} and so on.
\item[regular eliminator] in all the other cases. Here it must be
  possible to unify the term matched by
  \ssrC{e$_n$} with \ssrC{p$_m$}, the one matched by
  \ssrC{e$_{n-1}$} with \ssrC{p$_{m-1}$} and so on. Note that
  standard eliminators have the shape \ssrC{$\dots$forall x, P $\dots$ x}, thus
  \ssrC{e$_n$} is the pattern identifying the eliminated term, as expected.
\end{description}
As explained in  section~\ref{ssec:typefam}, the initial prefix of
\ssrC{e$_i$} can be omitted.

Here an example of a regular, but non trivial, eliminator:
\begin{lstlisting}
  Function |*plus*| (m n : nat) {struct n} : nat :=
     match n with 0 => m | S p => S (plus m p) end.
\end{lstlisting}
The type of \ssrC{plus_ind} is
\begin{lstlisting}
plus_ind : forall (m : nat) (P : nat -> nat -> Prop),
  (forall n : nat, n = 0 -> P 0 m) ->
  (forall n p : nat, n = p.+1 -> P p (plus m p) -> P p.+1 (plus m p).+1) ->
    forall n : nat, P n (plus m n)
\end{lstlisting}
Consider the following goal
\begin{lstlisting}
  Lemma |*exF*| x y z: plus (plus x y) z = plus x (plus y z).
\end{lstlisting}
The following tactics are all valid and perform the same elimination
on that goal.
\begin{lstlisting}
  elim/plus_ind: z / (plus _ z).
  elim/plus_ind: {z}(plus _ z).
  elim/plus_ind: {z}_.
  elim/plus_ind: z / _.
\end{lstlisting}
In the two latter examples, being the user provided pattern a wildcard, the
pattern inferred from the type of the eliminator is used instead.  For both
cases it is \ssrC{(plus _ _)} and matches the subterm \ssrC{plus (plus x y)$\;$z} thus
instantiating the latter \ssrC{_} with \ssrC{z}.  Note that the tactic
\ssrC{elim/plus_ind: y / _} would have resulted in an error, since \ssrC{y} and \ssrC{z}
do no unify but the type of the eliminator requires the second argument of
\ssrC{P} to be the same as the second argument of \ssrC{plus} in the second
argument of \ssrC{P}.

Here an example of a truncated eliminator. Consider the goal
\begin{lstlisting}
  p : nat_eqType
  n : nat
  n_gt0 : 0 < n
  pr_p : prime p
 =================
  p %| \prod_(i <- prime_decomp n | i \in prime_decomp n) i.1 ^ i.2 ->
    exists2 x : nat * nat, x \in prime_decomp n & p = x.1
\end{lstlisting}
and the tactic
\begin{lstlisting}
elim/big_prop: _ => [| u v IHu IHv | [q e] /=].
\end{lstlisting}
where the type of the eliminator is
\begin{lstlisting}
big_prop: forall (R : Type) (Pb : R -> Type) (idx : R) (op1 : R -> R -> R),
  Pb idx ->
  (forall x y : R, Pb x -> Pb y -> Pb (op1 x y)) ->
  forall (I : Type) (r : seq I) (P : pred I) (F : I -> R),
  (forall i : I, P i -> Pb (F i)) ->
    Pb (\big[op1/idx]_(i <- r | P i) F i)
\end{lstlisting}
Since the pattern for the argument of \ssrC{Pb} is not specified, the inferred one
is used instead: \ssrC{(\\big[_/_]_(i <- _ | _ i) _ i)}, and after the
introductions, the following goals are generated.
\begin{lstlisting}
subgoal 1 is:
 p %| 1 -> exists2 x : nat * nat, x \in prime_decomp n & p = x.1
subgoal 2 is:
 p %| u * v -> exists2 x : nat * nat, x \in prime_decomp n & p = x.1
subgoal 3 is:
 (q, e) \in prime_decomp n -> p %| q ^ e ->
   exists2 x : nat * nat, x \in prime_decomp n & p = x.1
\end{lstlisting}
Note that the pattern matching algorithm instantiated all the variables
occurring in the pattern.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Interpreting assumptions}\label{ssec:assumpinterp}
\idx{move/\dots{}}

Interpreting an assumption in the context of a proof is applying it a
correspondence lemma before generalizing, and/or decomposing it.
For instance, with the extensive use of boolean reflection (see
section \ref{ssec:boolrefl}), it is
quite frequent to need to decompose the logical interpretation of (the
boolean expression of) a
fact, rather than the fact itself.
This can be achieved by a combination of \ssrC{move : _ => _}
switches, like in the following script, where \ssrC{||} is a notation for
the boolean disjunction:
\begin{lstlisting}
  Variables P Q : bool -> Prop.
  Hypothesis |*P2Q*| : forall a b, P (a || b) -> Q a.

  Goal forall a, P (a || a) -> True.
  move=> a HPa; move: {HPa}(P2Q _ _ HPa) => HQa.
\end{lstlisting}
which transforms the hypothesis \ssrC{HPn : P n} which has been
introduced from the initial statement into \ssrC{HQn : Q n}.
This operation is so common that the tactic shell has
specific syntax for it.
The following scripts:
\begin{lstlisting}
  Goal forall a, P (a || a) -> True.
  move=> a HPa; move/P2Q: HPa => HQa.
\end{lstlisting}
or more directly:
\begin{lstlisting}
  Goal forall a, P (a || a) -> True.
  move=> a; move/P2Q=> HQa.
\end{lstlisting}
are equivalent to the former one. The former script shows how to
interpret a fact (already in the context), thanks to the discharge
tactical (see section \ref{ssec:discharge}) and the latter, how to
interpret the top assumption of a goal. Note
that the number of wildcards to be inserted to find the correct
application of the view lemma to the hypothesis has been automatically
inferred.

The view mechanism is compatible with the \ssrC{case} tactic and with the
equation name generation mechanism (see section \ref{ssec:equations}):
\begin{lstlisting}
  Variables P Q: bool -> Prop.
  Hypothesis |*Q2P*| : forall a b, Q (a || b) -> P a \/ P b.

  Goal forall a b, Q (a || b) -> True.
  move=> a b; case/Q2P=> [HPa | HPb].
\end{lstlisting}
creates two new subgoals whose contexts no more contain
\ssrC{HQ : Q (a || b)} but respectively \ssrC{HPa : P a} and
\ssrC{HPb : P b}. This view tactic
performs:
\begin{lstlisting}
  move=> a b HQ; case: {HQ}(Q2P _ _ HQ) => [HPa | HPb].
\end{lstlisting}

The term on the right of the \ssrC{/} view switch is called a \emph{view
  lemma}. Any \ssr{} term coercing to a product type can be used as a
view lemma.


The examples we have given so far explicitly provide the direction of the
translation to be performed. In fact, view lemmas need not to be
oriented. The view mechanism is able to detect which
application is relevant for the current goal. For instance, the
script:
\begin{lstlisting}
  Variables P Q: bool -> Prop.
  Hypothesis |*PQequiv*| : forall a b, P (a || b) <-> Q a.

  Goal forall a b, P (a || b) -> True.
  move=> a b; move/PQequiv=> HQab.
\end{lstlisting}
has the same behavior as the first example above.

The view mechanism can insert automatically a \emph{view hint} to
transform the double implication into the expected simple implication.
The last script is in fact equivalent to:
\begin{lstlisting}
  Goal forall a b, P (a || b) -> True.
  move=> a b; move/(iffLR (PQequiv _ _)).
\end{lstlisting}
where:
\begin{lstlisting}
  Lemma |*iffLR*| : forall P Q, (P <-> Q) -> P -> Q.
\end{lstlisting}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Specializing assumptions}
\idx{move/\dots{}}

The special case when the \emph{head symbol} of the view lemma is a
wildcard is used to interpret an assumption by \emph{specializing}
it. The view mechanism hence offers the possibility to
apply a higher-order assumption to some given arguments.

For example, the script:
\begin{lstlisting}
  Goal forall z, (forall x y, x + y = z -> z = x) -> z = 0.
  move=> z; move/(_ 0 z).
\end{lstlisting}
changes the goal into:
\begin{lstlisting}
  (0 + z = z -> z = 0) -> z = 0
\end{lstlisting}




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Interpreting goals}\label{ssec:goalinterp}

In a similar way, it is also often convenient to interpret a goal by changing
it into an equivalent proposition. The view mechanism of \ssr{} has a
special syntax \ssrC{apply/} for combining simultaneous goal
interpretation operations and
bookkeeping steps in a single tactic.

With the hypotheses of section \ref{ssec:assumpinterp}, the following
script, where \ssrL+~~+ denotes the boolean negation:
\begin{lstlisting}
  Goal forall a, P ((~~ a) || a).
  move=> a; apply/PQequiv.
\end{lstlisting}
transforms the goal into \ssrC{Q (~~ a)}, and is equivalent to:
\begin{lstlisting}
  Goal forall a, P ((~~ a) || a).
  move=> a; apply: (iffRL (PQequiv _ _)).
\end{lstlisting}
where \ssrC{iffLR} is the analogous of \ssrC{iffRL} for the converse
implication.

Any \ssr{} term whose type coerces to a double implication can be used
as a view for goal interpretation.

Note that the goal interpretation view mechanism supports both
\ssrC{apply} and \ssrC{exact} tactics. As expected, a goal interpretation
view command \ssrC{exact/$term$} should solve the current goal or it will
fail.


\emph{Warning} Goal interpretation view tactics are \emph{not} compatible
with the bookkeeping tactical \ssrC{=>} since this would be redundant with
the \ssrC{apply:} {\term} \ssrC{=> _} construction.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Boolean reflection}\label{ssec:boolrefl}
In the Calculus of Inductive Construction, there is
an obvious distinction between logical propositions and boolean values.
On the one hand, logical propositions are objects
of \emph{sort} \ssrC{Prop} which is the carrier of intuitionistic
reasoning. Logical connectives in \ssrC{Prop} are \emph{types}, which give precise
information on the structure of their proofs; this information is
automatically exploited by \Coq{} tactics. For example, \Coq{} knows that a
proof of \ssrL+A \/ B+ is either a proof of \ssrC{A} or a proof of \ssrC{B}.
The tactics \ssrC{left} and \ssrC{right} change the goal \ssrL+A \/ B+
to \ssrC{A} and \ssrC{B}, respectively; dualy, the tactic \ssrC{case} reduces the goal
\ssrL+A \/ B => G+ to two subgoals \ssrC{A => G} and \ssrC{B => G}.

On the other hand, \ssrC{bool} is an inductive \emph{datatype}
with two constructors \ssrC{true} and \ssrC{false}.
Logical connectives on \ssrC{bool} are \emph{computable functions}, defined by
their truth tables, using case analysis:
\begin{lstlisting}
  Definition (b1 || b2) := if b1 then true else b2.
\end{lstlisting}
Properties of such connectives are also established using case
analysis: the tactic \ssrC{by case: b} solves the goal
\begin{lstlisting}
  b || ~~ b = true
\end{lstlisting}
by replacing \ssrC{b} first by \ssrC{true} and then by \ssrC{false}; in either case,
the resulting subgoal reduces by computation to the trivial
\ssrC{true = true}.

Thus, \ssrC{Prop} and \ssrC{bool} are truly complementary: the former
supports robust natural deduction, the latter allows brute-force
evaluation.
\ssr{} supplies
a generic mechanism to have the best of the two worlds and move freely
from a propositional version of a
decidable predicate to its boolean version.

First, booleans are injected into propositions
using the coercion mechanism:
\begin{lstlisting}
  Coercion |*is_true*| (b : bool) := b = true.
\end{lstlisting}
This allows any boolean formula~\ssrC{b} to be used in a context
where \Coq{} would expect a proposition, e.g., after \ssrC{Lemma $\dots$ : }.
It is then interpreted as \ssrC{(is_true b)}, i.e.,
the  proposition \ssrC{b = true}. Coercions are elided by the pretty-printer,
so they are essentially transparent to the user.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The \ssrC{reflect} predicate}\label{ssec:reflpred}

To get all the benefits of the boolean reflection, it is in fact
convenient to introduce the following inductive predicate
\ssrC{reflect} to relate propositions and booleans:

\begin{lstlisting}
  Inductive |*reflect*| (P: Prop): bool -> Type :=
    | Reflect_true: P => reflect P true
    | Reflect_false: ~P => reflect P false.
\end{lstlisting}

The statement \ssrC{(reflect P b)} asserts that \ssrC{(is_true b)}
and \ssrC{P} are logically equivalent propositions.

For instance, the following lemma:
\begin{lstlisting}
  Lemma |*andP*|: forall b1 b2, reflect (b1 /\ b2) (b1 && b2).
\end{lstlisting}
relates the boolean conjunction \ssrC{&&} to
the logical one \ssrL+/\+.
Note that in \ssrC{andP}, \ssrC{b1} and \ssrC{b2} are two boolean variables and
the proposition \ssrL+b1 /\ b2+ hides two coercions.
The conjunction of \ssrC{b1} and \ssrC{b2} can then be viewed
as \ssrL+b1 /\ b2+  or as \ssrC{b1 && b2}.


Expressing logical equivalences through this family of inductive types
makes possible to take benefit from \emph{rewritable equations}
associated to the case analysis of \Coq{}'s inductive types.

Since the equivalence predicate is defined in \Coq{} as:
\begin{lstlisting}
  Definition |*iff*| (A B:Prop) := (A -> B) /\ (B -> A).
\end{lstlisting}
where \ssrC{/\\} is a notation for \ssrC{and}:
\begin{lstlisting}
  Inductive |*and*| (A B:Prop) : Prop :=
    conj : A -> B -> and A B
\end{lstlisting}

This make case analysis very different according to the way an
equivalence property has been defined.


For instance, if we have proved the lemma:
\begin{lstlisting}
  Lemma |*andE*|: forall b1 b2, (b1 /\ b2) <-> (b1 && b2).
\end{lstlisting}
let us compare the respective behaviours of \ssrC{andE} and \ssrC{andP} on a
goal:
\begin{lstlisting}
  Goal forall b1 b2, if (b1 && b2) then b1 else ~~(b1||b2).
\end{lstlisting}

The command:
\begin{lstlisting}
  move=> b1 b2; case (@andE b1 b2).
\end{lstlisting}
generates a single subgoal:
\begin{lstlisting}
  (b1 && b2 -> b1 /\ b2) -> (b1 /\ b2 -> b1 && b2) ->
                   if b1 && b2 then b1 else ~~ (b1 || b2)
\end{lstlisting}

while the command:
\begin{lstlisting}
  move=> b1 b2; case (@andP b1 b2).
\end{lstlisting}
generates two subgoals, respectively \ssrL+b1 /\ b2 -> b1+ and
\ssrL+~ (b1 /\ b2) -> ~~ (b1 || b2)+.



Expressing reflection relation through the \ssrC{reflect} predicate
is hence a very convenient way to deal with classical reasoning, by
case analysis. Using the \ssrC{reflect} predicate allows moreover to
program rich specifications inside
its two constructors, which will be automatically taken into account
during destruction. This formalisation style gives far more
efficient specifications than quantified (double) implications.


A naming convention in \ssr{} is to postfix the name of view lemmas with \ssrC{P}.
For example, \ssrC{orP} relates  \ssrC{||} and \ssrL+\/+, \ssrC{negP} relates
\ssrL+~~+ and \ssrL+~+.

The view mechanism is compatible with \ssrC{reflect} predicates.

For example, the script
\begin{lstlisting}
  Goal forall a b : bool, a -> b -> a /\\ b.
  move=> a b Ha Hb; apply/andP.
\end{lstlisting}
changes the goal \ssrL+a /\ b+ to \ssrC{a && b} (see section \ref{ssec:goalinterp}).

Conversely, the script
\begin{lstlisting}
  Goal forall a b : bool, a /\ b -> a.
  move=> a b; move/andP.
\end{lstlisting}
changes the goal \ssrL+a /\ b -> a+ into \ssrC{a && b -> a} (see section
\ref{ssec:assumpinterp}).


The same tactics can also be used to perform the converse
operation, changing a boolean conjunction into a logical one. The view
mechanism guesses the direction of the
transformation to be used i.e., the constructor of the \ssrC{reflect}
predicate which should be chosen.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{General mechanism for interpreting goals and assumptions}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Specializing assumptions}
\idx{move/\dots{}}

The \ssr{}
tactic:

  \ssrC{move/(_} \ssrN[1]{term} $\dots$ \ssrN[n]{term}\ssrC{)}

\noindent
is equivalent to the tactic:

  \ssrC{intro top; generalize (top} \ssrN[1]{term} $\dots$ \ssrN[n]{term}\ssrC{); clear top.}

\noindent
where \ssrC{top} is a fresh name for introducing the top assumption of
the current goal.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Interpreting assumptions}
\label{sssec:hypview}
The general form of an assumption view tactic is:

\begin{center}
 \optional{\ssrC{move} {\optsep} \ssrC{case}} \ssrC{/} \ssrN[0]{term}
\end{center}

The term \ssrN[0]{term}, called the \emph{view lemma} can be:
\begin{itemize}
\item a (term coercible to a) function;
\item a (possibly quantified) implication;
\item a (possibly quantified) double implication;
\item a (possibly quantified) instance of the \ssrC{reflect} predicate
  (see section \ref{ssec:reflpred}).
\end{itemize}

Let \ssrC{top} be the top assumption in the goal.

There are three steps in the behaviour of an assumption view tactic:
\begin{itemize}
\item It first introduces \ssrL+top+.
\item If the type of \ssrN[0]{term} is neither a double implication nor
  an instance of the \ssrC{reflect} predicate, then the tactic
  automatically generalises a term of the form:
  
\begin{center}
  \ssrC{(}\ssrN[0]{term} \ssrN[1]{term} $\dots$ \ssrN[n]{term}\ssrC{)}
\end{center}
  
  where the terms \ssrN[1]{term} $\dots$ \ssrN[n]{term} instantiate the
  possible quantified variables of \ssrN[0]{term}, in order for
  \ssrC{(}\ssrN[0]{term} \ssrN[1]{term} $\dots$ \ssrN[n]{term} \ssrC{top)} to be well typed.
\item If the type of $\ssrN[0]{term}$ is an equivalence, or
  an instance of the \ssrC{reflect} predicate, it generalises a term of
  the form:
  \begin{center}
  (\ssrN[vh]{term} (\ssrN[0]{term} \ssrN[1]{term} $\dots$ \ssrN[n]{term}))
  \end{center}
  where the term \ssrN[vh]{term} inserted is called an
  \emph{assumption interpretation view hint}.
\item It finally clears \ssrC{top}.
\end{itemize}
For a \ssrC{case/}\ssrN[0]{term} tactic, the generalisation step is
replaced by a case analysis step.

\emph{View hints} are declared by the user (see section
\ref{ssec:vhints}) and are stored in the \ssrC{Hint View} database.
The proof engine automatically
detects from the shape of the top assumption \ssrC{top} and of the view
lemma $\ssrN[0]{term}$ provided to the tactic the appropriate view hint in
the database to be inserted.

If $\ssrN[0]{term}$ is a double implication, then the view hint \ssrC{A} will
be one of the defined view hints for implication. These hints are by
default the ones present in the file {\tt ssreflect.v}:
\begin{lstlisting}
  Lemma |*iffLR*| : forall P Q, (P <-> Q) -> P -> Q.
\end{lstlisting}
which transforms a double  implication into the left-to-right one, or:
\begin{lstlisting}
  Lemma |*iffRL*| : forall P Q, (P <-> Q) -> Q -> P.
\end{lstlisting}
which produces the converse implication. In both cases, the two first
\ssrC{Prop} arguments are implicit.

If $\ssrN[0]{term}$ is an instance of the \ssrC{reflect} predicate, then \ssrC{A}
will be one of the defined view hints  for the \ssrC{reflect}
predicate,  which are by
default the ones present in the file {\tt ssrbool.v}.
These hints are not only used for choosing the appropriate direction of
the translation, but they also allow complex transformation, involving
negations.
 For instance the hint:
\begin{lstlisting}
  Lemma |*introN*| : forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~ b.
\end{lstlisting}
makes the following script:
\begin{lstlisting}
  Goal forall a b : bool, a -> b -> ~~ (a && b).
  move=> a b Ha Hb. apply/andP.
\end{lstlisting}
transforms the goal into \ssrC{ \~ (a /\ b)}.
In fact\footnote{The current state of the proof shall be displayed by
  the \ssrC{Show Proof} command of \Coq{} proof mode.}
this last script does not exactly use the hint \ssrC{introN}, but the
more general hint:
\begin{lstlisting}
  Lemma |*introNTF*| : forall (P : Prop) (b c : bool),
      reflect P b -> (if c then ~ P else P) -> ~~ b = c
\end{lstlisting}
The lemma \ssrL+|*introN*|+ is an instantiation of \ssrC{introNF} using
 \ssrC{c := true}.

Note that views, being part of \ssrN{i-pattern}, can be used to interpret
assertions too. For example the following script asserts \ssrC{a \&\& b}
but actually used its propositional interpretation.
\begin{lstlisting}
  Lemma |*test*| (a b : bool) (pab : b && a) : b.
  have /andP [pa ->] : (a && b) by rewrite andbC.
\end{lstlisting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsubsection*{Interpreting goals}
\idx{apply/\dots{}}

A goal interpretation view tactic of the form:

\begin{center}
	\ssrC{apply/} \ssrN[0]{term}
\end{center}
applied to a goal \ssrC{top} is interpreted in the following way:
\begin{itemize}
\item If the type of $\ssrN[0]{term}$ is not an instance of the
  \ssrC{reflect} predicate, nor an equivalence,
  then the term $\ssrN[0]{term}$ is applied to the current goal \ssrC{top},
  possibly inserting implicit arguments.
\item If the type of $\ssrN[0]{term}$ is an instance of the \ssrC{reflect}
  predicate or an equivalence, then
a \emph{goal interpretation view hint} can possibly be inserted, which
corresponds to the application of a term
\ssrC{($\ssrN[vh]{term}$ ($\ssrN[0]{term}$ _ $\dots$ _))} to the current
goal, possibly inserting implicit arguments.
\end{itemize}

Like assumption interpretation view hints, goal interpretation ones
are user defined lemmas stored (see section \ref{ssec:vhints}) in the
\ssrC{Hint View} database bridging
the possible gap between the type of $\ssrN[0]{term}$ and the type of the
goal.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Interpreting equivalences}
\idx{apply/\dots{}/\dots{}}

Equivalent boolean propositions are simply \emph{equal} boolean terms.
A special construction helps the user to prove boolean equalities by
considering them as logical double implications (between their coerced
versions), while
performing at the same time logical operations on both sides.

The syntax of double views is:
\begin{center}
 \ssrC{apply/} \ssrN[l]{term} \ssrC{/} \ssrN[r]{term}
\end{center}

The term \ssrN[l]{term} is the view lemma applied to the left hand side of the
equality, \ssrN[r]{term} is the one applied to the right hand side.

In this context, the identity view:
\begin{lstlisting}
Lemma |*idP*| : reflect b1 b1.
\end{lstlisting}
is useful, for example the tactic:
\begin{lstlisting}
  apply/idP/idP.
\end{lstlisting}
transforms the goal
\ssrL+~~ (b1 || b2)= b3+
 into two subgoals, respectively
 \ssrL+~~  (b1 || b2) -> b3+ and \\
\ssrL+b3 -> ~~  (b1 || b2).+

The same goal can be decomposed in several ways, and the user may
choose the most convenient interpretation. For instance, the tactic:
\begin{lstlisting}
  apply/norP/idP.
\end{lstlisting}
applied on the same goal \ssrL+~~ (b1 || b2) = b3+ generates the subgoals
\ssrL+~~  b1 /\ ~~  b2 -> b3+ and\\
\ssrL+b3 -> ~~  b1 /\ ~~  b2+.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Declaring new \ssrC{Hint View}s}\label{ssec:vhints}
\idxC{Hint View}

The database of hints for the view mechanism is extensible via a
dedicated vernacular command. As library {\tt ssrbool.v} already
declares a corpus of hints, this feature is probably useful only for
users who define their own logical connectives. Users can declare
their own hints following the syntax used in {\tt ssrbool.v}:

\begin{center}
  \ssrC{Hint View for} {\tac} \ssrC{/} \ssrN{ident} \optional{\ssrC{|}{\naturalnumber}}
\end{center}

  where {\tac}$\in \{$\ssrC{move, apply}$\}$, \ssrN{ident} is the
name of the lemma to be declared as a hint, and ${\naturalnumber}$ a natural
number. If \ssrL+move+ is used as {\tac}, the hint is declared for
assumption interpretation tactics, \ssrL+apply+ declares hints for goal
interpretations.
Goal interpretation view hints are declared for both simple views and
left hand side views. The optional natural number ${\naturalnumber}$ is the
number of implicit arguments to be considered for the declared hint
view lemma \ssrC{name_of_the_lemma}.

The command:

\begin{center}
  \ssrC{Hint View for apply//} \ssrN{ident}\optional{\ssrC{|}{\naturalnumber}}.
\end{center}

with a double slash \ssrL+//+, declares hint views for right hand sides of
double views.


\noindent See the files {\tt ssreflect.v} and {\tt ssrbool.v} for examples.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Multiple views}\label{ssec:multiview}

The hypotheses and the goal can be interpreted applying multiple views in
sequence. Both \ssrC{move} and \ssrC{apply} can be followed by an arbitrary number
of \ssrC{/}$\ssrN[i]{term}$. The main difference between the following two tactics
\begin{lstlisting}
  apply/v1/v2/v3.
  apply/v1; apply/v2; apply/v3.
\end{lstlisting}
is that the former applies all the views to the principal goal.
Applying a view with hypotheses generates new goals, and the second line
would apply the view \ssrC{v2} to all the goals generated by \ssrC{apply/v1}.
Note that the NO-OP intro pattern \ssrC{-} can be used to separate two
views, making the two following examples equivalent:
\begin{lstlisting}
  move=> /v1; move=> /v2.
  move=> /v1-/v2.
\end{lstlisting}

The tactic \ssrC{move} can be used together with the \ssrC{in}
tactical to pass a given hypothesis to a lemma. For example, if
\ssrC{P2Q : P -> Q } and \ssrC{Q2R : Q -> R}, the following
tactic turns the hypothesis \ssrC{p : P} into \ssrC{P : R}.
\begin{lstlisting}
  move/P2Q/Q2R in p.
\end{lstlisting}

If the list of views is of length two, \ssrC{Hint View}s for interpreting
equivalences are indeed taken into account, otherwise only single
\ssrC{Hint View}s are used.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{\ssr{} searching tool}
\idxC{Search \dots{}}

\ssr{} proposes an extension of the \ssrC{Search} command. Its syntax is:

\begin{center}
	\ssrC{Search} \optional{\ssrN{pattern}} \optional{\optional{\ssrC{\-}} \optional{\ssrN{string}\optional{\ssrC{\%}\ssrN{key}} {\optsep} \ssrN{pattern}}}$^*$ \optional{\ssrC{in} \optional{\optional{\ssrC{\-}} \ssrN{name} }$^+$}
\end{center}

% \begin{lstlisting}
%   Search [[\~]\ssrN{string}]$^*$ [\ssrN{pattern}] [[$\ssrN[1]{pattern} \dots $ $\ssrN[n]{pattern}$]] $[[$inside$|$outside$]$ $M_1 \dots M_n$].
% \end{lstlisting}

% This tactic returns the list of defined constants matching the
%  given criteria:
% \begin{itemize}
% \item \ssrL+[[-]\ssrN{string}]$^*$+ is an open sequence of strings, which sould
%   all appear in the name of the returned constants. The optional \ssrL+-+
%   prefixes strings that are required  \emph{not} to appear.
% % \item \ssrN{pattern} should be a subterm of the
% %   \emph{conclusion} of the lemmas found by the command. If a lemma features
% %   an occurrence
% %   of this pattern only in one or several of its assumptions, it will not be
% %   selected by the searching tool.
% \item
% \ssrL=[$\ssrN{pattern}^+$]=
% is a list of \ssr{} terms, which may
% include types, that are required to appear in the returned constants.
% Terms with holes should be surrounded by parentheses.
% \item $\ssrC{in}\ [[\ssrC{\-}]M]^+$ limits the search to the signature
%   of open modules given in the list, but the ones preceeded by the
%   $\ssrC{\-}$ flag. The
%   command:
% \begin{lstlisting}
%   Search in M.
% \end{lstlisting}
% is hence a way of obtaining the complete signature of the module \ssrL{M}.
% \end{itemize}
where \ssrN{name} is the name of an open module.
This command search returns the list of lemmas:
\begin{itemize}
\item whose \emph{conclusion} contains a subterm matching the optional
  first \ssrN{pattern}. A $\ssrC{-}$ reverses the test, producing the list
  of lemmas whose conclusion does not contain any subterm matching
  the pattern;
\item whose name contains the given string. A $\ssrC{-}$ prefix reverses
  the test, producing the list of lemmas whose name does not contain the
  string. A string that contains symbols or
is followed by a scope \ssrN{key}, is interpreted as the constant whose
notation involves that string (e.g., \ssrL=+= for \ssrL+addn+), if this is
unambiguous; otherwise the diagnostic includes the output of the
\ssrC{Locate} vernacular command.

\item whose statement, including assumptions and types, contains a
  subterm matching the next patterns. If a pattern is prefixed by
  $\ssrC{-}$, the test is reversed;
\item contained in the given list of modules, except the ones in the
  modules prefixed by a $\ssrC{-}$.
\end{itemize}

Note that:
\begin{itemize}
\item As for regular terms, patterns can feature scope
  indications. For instance, the command:
\begin{lstlisting}
  Search _ (_ + _)%N.
\end{lstlisting}
lists all the lemmas whose statement (conclusion or hypotheses)
involve an application of the binary operation denoted by the infix
\ssrC{+} symbol in the \ssrC{N} scope (which is \ssr{} scope for natural numbers).
\item Patterns with holes should be surrounded by parentheses.
\item Search always volunteers the expansion of the notation, avoiding the
  need to execute Locate independently. Moreover, a string fragment
  looks for any notation that contains fragment as
  a substring. If the \ssrL+ssrbool+ library is imported, the command:
\begin{lstlisting}
  Search "~~".
\end{lstlisting}
answers :
\begin{lstlisting}
"~~" is part of notation (~~ _)
In bool_scope, (~~ b) denotes negb b
negbT  forall b : bool, b = false -> ~~ b
contra  forall c b : bool, (c -> b) -> ~~ b -> ~~ c
introN  forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~ b
\end{lstlisting}
 \item A diagnostic is issued if there are different matching notations;
  it is an error if all matches are partial.
\item Similarly, a diagnostic warns about multiple interpretations, and
  signals an error if there is no default one.
\item The command  \ssrC{Search in M.}
is a way of obtaining the complete signature of the module \ssrL{M}.
\item Strings and pattern indications can be interleaved, but the
  first indication has a special status if it is a pattern, and only
  filters the conclusion of lemmas:
\begin{itemize}
  \item The command :
    \begin{lstlisting}
      Search (_ =1 _) "bij".
    \end{lstlisting}
lists all the lemmas whose conclusion features a '$\ssrC{=1}$' and whose
name contains the string \verb+bij+.
\item The command :
    \begin{lstlisting}
      Search  "bij" (_ =1 _).
    \end{lstlisting}
lists all the lemmas whose statement, including hypotheses, features a
'$\ssrC{=1}$' and whose name contains the string \verb+bij+.

\end{itemize}

\end{itemize}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Synopsis and Index}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{Parameters}

\begin{minipage}[c]{\textwidth}\renewcommand{\footnoterule}{}
\begin{longtable}{lcl}
\ssrN{d-tactic} && one of the
  \ssrC{elim}, \ssrC{case}, \ssrC{congr}, \ssrC{apply}, \ssrC{exact}
  and \ssrC{move} \ssr{} tactics \\
\ssrN{fix-body} && standard \Coq{} \textit{fix\_body}\\
\ssrN{ident} && standard \Coq{} identifier\\
\ssrN{int} && integer literal \\
\ssrN{key} && notation scope\\
\ssrN{name} && module name\\
${\naturalnumber}$ && \ssrN{int} or Ltac variable denoting a standard \Coq{} numeral\footnote{The name of this Ltac variable should not be the name of a tactic which can be followed by a bracket
  \ssrL+[+, like  \ssrL+do+, \ssrL+ have+,\dots}\\
\ssrN{pattern} && synonym for {\term}\\
\ssrN{string} && standard \Coq{} string\\
{\tac} && standard \Coq{} tactic or \ssr{} tactic\\
{\term} & \hspace{1cm} & Gallina term, possibly containing wildcards\\
%\ssrN{view} && global constant\\
\end{longtable}
\end{minipage}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{Items and switches}

\begin{longtable}{lclr}
\ssrN{binder}  & {\ident} {\optsep} \ssrC{(} {\ident} \optional{\ssrC{:} {\term} } \ssrC{)} & binder& p. \pageref{ssec:pose}\\
\\
\ssrN{clear-switch} & \ssrC{\{} {\ident}$^+$ \ssrC{\}} & clear switch & p. \pageref{ssec:discharge}\\
\\
\ssrN{c-pattern} & \optional{{\term} \ssrC{in} {\optsep} {\term} \ssrC{as}} {\ident} \ssrC{in} {\term} & context pattern & p. \pageref{ssec:rewp} \\
\\
\ssrN{d-item} & \optional{\ssrN{occ-switch} {\optsep} \ssrN{clear-switch}} \optional{{\term} {\optsep} \ssrC{(}\ssrN{c-pattern}\ssrC{)}} & discharge item & p. \pageref{ssec:discharge}\\
\\
\ssrN{gen-item}  & \optional{\ssrC{@}}{\ident} {\optsep} \ssrC{(}{\ident}\ssrC{)} {\optsep} \ssrC{(}\optional{\ssrC{@}}{\ident} \ssrC{:=} \ssrN{c-pattern}\ssrC{)} & generalization item & p. \pageref{ssec:struct}\\
\\
\ssrN{i-pattern} & {\ident} {\optsep} \ssrC{_} {\optsep} \ssrC{?} {\optsep} \ssrC{*} {\optsep} \optional{\ssrN{occ-switch}}\ssrC{->} {\optsep} \optional{\ssrN{occ-switch}}\ssrC{<-} {\optsep} &  intro pattern & p. \pageref{ssec:intro}\\
& \ssrC{[} \ssrN{i-item}$^*$ \ssrC{|} $\dots$ \ssrC{|} \ssrN{i-item}$^*$ \ssrC{]} {\optsep} \ssrC{-} {\optsep} \ssrC{[:} {\ident}$^+$\ssrC{]} &\\
\\
\ssrN{i-item} & \ssrN{clear-switch} {\optsep} \ssrN{s-item} {\optsep} \ssrN{i-pattern} {\optsep} \ssrC{/}{\term} & intro item & p. \pageref{ssec:intro}\\
\\
\ssrN{int-mult} & \optional{{\naturalnumber}} \ssrN{mult-mark} & multiplier & p. \pageref{ssec:iter}\\
\\
\ssrN{occ-switch} & \ssrC{\{} \optional{\ssrC{+} {\optsep} \ssrC{-}} {\naturalnumber}$^*$\ssrC{\}} & occur. switch &  p. \pageref{sssec:occselect}\\
\\
\ssrN{mult} & \optional{{\naturalnumber}} \ssrN{mult-mark} & multiplier & p. \pageref{ssec:iter}\\
\\
\ssrN{mult-mark} &  \ssrC{?} {\optsep} \ssrC{!} & multiplier mark &  p. \pageref{ssec:iter}\\
\\
\ssrN{r-item} &  \optional{\ssrC{/}} {\term} {\optsep} \ssrN{s-item} & rewrite item & p. \pageref{ssec:extrw}\\
\\
\ssrN{r-prefix} & \optional{\ssrC{-}} \optional{\ssrN{int-mult}} \optional{\ssrN{occ-switch} {\optsep} \ssrN{clear-switch}} \optional{\ssrC{[}\ssrN{r-pattern}\ssrC{]}} & rewrite prefix & p. \pageref{ssec:extrw}\\
\\
\ssrN{r-pattern} & {\term} {\optsep} \ssrN{c-pattern} {\optsep} \ssrC{in} \optional{{\ident} \ssrC{in}} {\term} & rewrite pattern & p. \pageref{ssec:extrw}\\
\\
\ssrN{r-step} & \optional{\ssrN{r-prefix}}\ssrN{r-item} & rewrite step & p. \pageref{ssec:extrw}\\
\\
\ssrN{s-item} & \ssrC{/=} {\optsep} \ssrC{//} {\optsep} \ssrC{//=} & simplify switch & p. \pageref{ssec:intro}\\
\\
\end{longtable}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{Tactics}
\emph{Note}: \ssrC{without loss} and \ssrC{suffices} are synonyms for \ssrC{wlog} and
\ssrC{suff} respectively.

\begin{longtable}{llr}
\ssrC{move} & \textcolor{dkblue}{\texttt{idtac}} or \ssrC{hnf}& p. \pageref{ssec:profstack} \\
\ssrC{apply} & application & p. \pageref{ssec:basictac}\\
\ssrC{exact} &&\\
\ssrC{abstract} && p. \pageref{ssec:abstract}, \pageref{sec:havetransparent}\\
\\
\ssrC{elim} & induction & p. \pageref{ssec:basictac}\\
\ssrC{case} & case analysis  & p. \pageref{ssec:basictac}\\
\\
\ssrC{rewrite} \ssrN{rstep}$^+$ & rewrite& p. \pageref{ssec:extrw}\\
\\
\ssrC{have} \ssrN{i-item}$^*$ \optional{\ssrN{i-pattern}} \optional{\ssrN{s-item} {\optsep} \ssrN{binder}$^+$} \optional{\ssrC{:} {\term}} \ssrC{:=} {\term} & forward & p. \pageref{ssec:struct}\\
\ssrC{have} \ssrN{i-item}$^*$ \optional{\ssrN{i-pattern}} \optional{\ssrN{s-item}{\optsep} \ssrN{binder}$^+$} \ssrC{:} {\term} \optional{\ssrC{by} {\tac}} & chaining & \\
\ssrC{have suff} \optional{\ssrN{clear-switch}} \optional{\ssrN{i-pattern}} \optional{\ssrC{:} {\term}} \ssrC{:=} {\term} & & \\
\ssrC{have suff} \optional{\ssrN{clear-switch}} \optional{\ssrN{i-pattern}} \ssrC{:} {\term} \optional{\ssrC{by} {\tac}} & & \\
\ssrC{gen have} \optional{{\ident}\ssrC{,}} \optional{\ssrN{i-pattern}} \ssrC{:} \ssrN{gen-item}$^+$ \ssrC{/} {\term} \optional{\ssrC{by} {\tac}} & & \\
\\
\ssrC{wlog} \optional{\ssrC{suff}} \optional{\ssrN{i-item}} \ssrC{:} \optional{\ssrN{gen-item}{\optsep} \ssrN{clear-switch}}$^*$ \ssrC{/} {\term} & specializing &  p. \pageref{ssec:struct} \\
\\
\ssrC{suff} \ssrN{i-item}$^*$ \optional{\ssrN{i-pattern}} \optional{\ssrN{binder}$^+$} \ssrC{:} {\term} \optional{\ssrC{by} {\tac}} & backchaining & p. \pageref{ssec:struct}\\
\ssrC{suff} \optional{\ssrC{have}} \optional{\ssrN{clear-switch}} \optional{\ssrN{i-pattern}} \ssrC{:} {\term} \optional{\ssrC{by} {\tac}} & & \\
\\
\ssrC{pose} {\ident} \ssrC{:=} {\term} & local definition& p. \pageref{ssec:pose}\\
\ssrC{pose} {\ident} \ssrN{binder}$^+$ \ssrC{:=} {\term} & \rlap{local function definition}& \\
\ssrC{pose fix} \ssrN{fix-body} & \rlap{local fix definition} & \\
\ssrC{pose cofix} \ssrN{fix-body} & \rlap{local cofix definition} &  \\
\\
\ssrC{set} {\ident} \optional{\ssrC{:} {\term}} \ssrC{:=} \optional{\ssrN{occ-switch}} \optional{{\term}{\optsep} \ssrC{(}\ssrN{c-pattern}\ssrC{)}} & abbreviation&p. \pageref{ssec:set}\\
\\
\ssrC{unlock} \optional{\ssrN{r-prefix}]{\ident}}$^*$ & unlock & p. \pageref{ssec:lock}\\
\\
\ssrC{congr} \optional{\naturalnumber} {\term} & congruence& p. \pageref{ssec:congr}\\
\end{longtable}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{Tacticals}

\begin{longtable}{lclr}
\ssrN{d-tactic} \optional{\ident} \ssrC{:} \ssrN{d-item}$^{+}$ \optional{\ssrN{clear-switch}} & & discharge &  p. \pageref{ssec:discharge}\\
\\
{\tac} \ssrC{=>} \ssrN{i-item}$^+$ && introduction & p. \pageref{ssec:intro}\\
\\
{\tac} \ssrC{in} \optional{\ssrN{gen-item} {\optsep} \ssrN{clear-switch}}$^+$  \optional{\ssrC{*}} && localization & p. \pageref{ssec:gloc}\\
\\
\ssrC{do} \optional{\ssrN{mult}} \ssrC{[} \nelist{\tac}{|} \ssrC{]}&& iteration & p. \pageref{ssec:iter}\\
\ssrC{do} \ssrN{mult} {\tac} &&& \\
\\
{\tac} \ssrC{ ; first} \optional{\naturalnumber} \ssrC{[}\nelist{\tac}{|}\ssrC{]} && selector & p. \pageref{ssec:select}\\
{\tac} \ssrC{ ; last}  \optional{\naturalnumber} \ssrC{[}\nelist{\tac}{|}\ssrC{]} \\
{\tac} \ssrC{ ; first} \optional{\naturalnumber} \ssrC{last} && subgoals & p. \pageref{ssec:select}\\
{\tac} \ssrC{; last} \optional{\naturalnumber} \ssrC{first} && rotation & \\
\\
\ssrC{by [} \nelist{\tac}{|} \ssrC{]} && closing & p. \pageref{ssec:termin}\\
\ssrC{by []} \\
\ssrC{by} {\tac} \\
\end{longtable}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection*{Commands}
\begin{longtable}{lclr}
\ssrL+Hint View for+ \optional{\ssrL+move+ {\it |} \ssrL+apply+} {\tt /} {\ident} \optional{{\tt|} {\naturalnumber}} && view hint
declaration & p. \pageref{ssec:vhints}\\
\\
\ssrL+Hint View for apply//+ {\ident} \optional{{\tt|}{\naturalnumber}} && right hand side double
 & p. \pageref{ssec:vhints}\\
&&  view hint declaration &\\
\\
%\ssrL+Import Prenex Implicits+ && enable prenex implicits &
%p. \pageref{ssec:parampoly}\\
%\\
\ssrL+Prenex Implicits+ {\ident}$^+$ & \hspace{.6cm} & prenex implicits decl.
 & p. \pageref{ssec:parampoly}\\

\end{longtable}

\iffalse

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Changes}

\subsection{\ssr{} version 1.3}
All changes are retrocompatible extensions but for:
\begin{itemize}
\item Occurrences in the type family switch now refer only to the goal, while
      before they used to refer also to the types in the abstractions of the
      predicate used by the eliminator. This bug used to affect lemmas like
      \ssrC{boolP}. See the relative comments in \ssrC{ssrbool.v}.
\item Clear switches can only mention existing hypothesis and
      otherwise fail. This can in particular affect intro patterns
      simultaneously applied to several goals.
      % commit: 2686
\item A bug in the \ssrC{rewrite} tactic allowed to
      instantiate existential metavariables occurring in the goal.
      This is not the case any longer (see section~\ref{ssec:rewcaveats}).
\item The \ssrC{fold} and \ssrC{unfold} \ssrN{r-items} for \ssrC{rewrite} used to
      fail silently when used in combination with a \ssrN{r-pattern} matching no
      goal subterm. They now fail. The old behavior can be obtained using
      the \ssrC{?} multiplier (see section~\ref{ssec:extrw}).
\item \Coq{} 8.2 users with a statically linked toplevel must comment out the\\
      \ssrC{Declare ML Module "ssreflect".}\\
      line at the beginning of \ssrC{ssreflect.v} to compile the 1.3 library.
\end{itemize}
New features:
\begin{itemize}
\item Contextual \ssrC{rewrite} patterns.
      The context surrounding the redex can now be used to specify which
      redex occurrences should be rewritten (see section~\ref{ssec:rewp}).\\
      \ssrC{rewrite [in X in _ = X]addnC.}
      % commit: 2690, 2689, 2718, 2733
\item Proof irrelevant interpretation of goals with existential metavariables.
      Goals containing an existential metavariable of sort \ssrC{Prop} are
      generalized over it, and a new goal for the missing subproof is
      generated (see page~\pageref{sssec:apply} and
      section~\ref{ssec:rewcaveats}).\\
      \ssrC{apply: (ex_intro _ (@Ordinal _ y _)).}\\
      \ssrC{rewrite insubT.}
      % commit: 2553, 2544, 2543, 2733
\item Views are now part of \ssrN{i-pattern} and can thus be used
      inside intro patterns (see section~\ref{ssec:intro}).\\
      \ssrC{move=> a b /andP [Ha Hb].}
      % commit: 2720
\item Multiple views for \ssrC{move}, \ssrC{move $\dots$ in} and \ssrC{apply}
      (see section~\ref{ssec:multiview}).\\
      \ssrC{move/v1/v2/v3.}\\
      \ssrC{move/v1/v2/v3 in H.}\\
      \ssrC{apply/v1/v2/v3.}
      % commit: 2720
\item \ssrC{have} and \ssrC{suff} idiom with view (see section~\ref{sssec:hypview}).
\begin{lstlisting}
  Lemma |*test*| (a b : bool) (pab : a && b) : b.
  have {pab} /= /andP [pa ->] // : true && (a && b) := pab.
\end{lstlisting}
      % commit: 2726
\item \ssrC{have suff}, \ssrC{suff have} and \ssrC{wlog suff} forward reasoning
      tactics (see section~\ref{ssec:struct}).\\
      \ssrC{have suff H : P.}
      % commit: 2633
\item Binders support in \ssrC{have} (see section~\ref{sssec:have}).\\
      \ssrC{have H x y (r : R x y) : P x -> Q y.}
      % commit: 2633
\item Deferred clear switches. Clears are deferred to the end of the
      intro pattern. In the meanwhile, cleared variables are still
      part of the context, thus the goal can mention them, but are
      renamed to non accessible dummy names (see section~\ref{ssec:intro}).\\
      \ssrC{suff: G \\x H = K; first case/dprodP=> \{G H\} [[G H -> -> defK]].}
      % commit: 2660
\item Relaxed alternation condition in intro patterns. The
      \ssrN{i-item} grammar rule is simplified (see section~\ref{ssec:intro}).\\
       \ssrC{move=> a \{H\} /= \{H1\} // b c /= \{H2\}.}
      % commit: 2713
\item Occurrence selection for \ssrC{->} and \ssrC{<-} intro pattern
       (see section~\ref{ssec:intro}).\\
      \ssrC{move=> a b H \{2\}->.}
      % commit: 2714
\item Modifiers for the discharging '\ssrC{:}' and \ssrC{in} tactical to override
      the default behavior when dealing with local definitions (let-in):
      \ssrC{@f} forces the body of \ssrC{f} to be kept, \ssrC{(f)} forces the body of
      \ssrC{f} to be dropped  (see sections~\ref{ssec:discharge}
      and~\ref{ssec:gloc}).\\
      \ssrC{move: x y @f z.}\\
      \ssrC{rewrite rule in (f) $\;\;$H.}
      %commit: 2659, 2710
\item Type family switch in \ssrC{elim} and \ssrC{case}
      can contain patterns with occurrence switch
      (see section~\ref{ssec:typefam}).\\
      \ssrC{case: \{2\}(_ == x) / eqP.}
      % commit: 2593, 2598, 2539, 2538, 2527, 2529
\item Generic second order predicate support for \ssrC{elim}
      (see section~\ref{sec:views}).\\
      \ssrC{elim/big\_prop: _}
      % commit: 2767
\item The \ssrC{congr} tactic now also works on products (see
      section~\ref{ssec:congr}).
\begin{lstlisting}
  Lemma |*test*| x (H : P x) : P y.
  congr (P _): H.
\end{lstlisting}
      % commit: 2608
\item Selectors now support Ltac variables
      (see section~\ref{ssec:select}).\\
      \ssrC{let n := 3 in tac; first n last.}
      % commit: 2725
\item Deprecated use of \ssrC{Import Prenex Implicits} directive.
      It must be replaced with the \Coq{} \ssrC{Unset Printing
        Implicit Defensive} vernacular command.
\item New synonym \ssrC{Canonical} for \ssrC{Canonical Structure}.
\end{itemize}
\subsection{\ssr{} version 1.4}
New features:
\begin{itemize}
\item User definable recurrent contexts (see section~\ref{ssec:rewp}).\\
      \ssrC{Notation RHS := (X in _ = X)\%pattern}
\item Contextual patterns in
      \ssrC{set} and `\ssrC{:}' (see section~\ref{ssec:rewp}).\\
      \ssrC{set t := (a + _ in RHS)}
\item NO-OP intro pattern (see section~\ref{ssec:intro}).\\
      \ssrC{move=> /eqP-H /fooP-/barP}
\item \ssrC{if $\ {\term}\ $ isn't $\ \ssrN{pattern}\ $ then $\ {\term}\ $
  else $\ {\term}\ $} notation (see section~\ref{ssec:patcond}).\\
      \ssrC{if x isn't Some y then simple else complex y}
\end{itemize}
\subsection{\ssr{} version 1.5}
Incompatibilities:
\begin{itemize}
\item The \ssrC{have} tactic now performs type classes resolution.  The old
	behavior can be restored with \ssrC{Set SsrHave NoTCResolution}
\end{itemize}
Fixes:
\begin{itemize}
\item The \ssrC{let foo := type of t in} syntax of standard \ssrC{Ltac} has
	been made compatible with \ssr{} and can be freely used even if
	the \ssr{} plugin is loaded
\end{itemize}
New features:
\begin{itemize}
\item Generalizations supported in have (see section~\ref{ssec:struct}).\\
      \ssrC{generally have hx2px, pa : a ha / P a.}
\item Renaming and patterns in wlog (see section~\ref{ssec:struct} and
  page \pageref{par:advancedgen}).\\
      \ssrC{wlog H : (n := m)$\;$ (x := m + _)$\;$ / T x}.\\
      \ssrC{wlog H : (n := m)$\;$ (@ldef := secdef m)$\;$ / T x}.
\item Renaming, patterns and clear switches in \ssrC{in}
      tactical (see section~\ref{ssec:gloc}).\\
      \ssrC{$\dots$ in H1 \{H2\} (n := m).}
\item Handling of type classes in \ssrC{have}
	(see page~\pageref{ssec:havetcresolution}).\\
	\ssrC{have foo : ty. (* TC inference for ty *)}\\
	\ssrC{have foo : ty := . (* no TC inference for ty *)}\\
	\ssrC{have foo : ty := t. (* no TC inference for ty and t *)}\\
	\ssrC{have foo := t. (* no TC inference for t *)}
\item Transparent flag for \ssrC{have} to generate a \ssrC{let in} context entry
	(see page~\pageref{sec:havetransparent}).\\
        \ssrC{have @i : 'I\_n by apply: (Sub m); auto.}
\item Intro pattern \ssrC{[: foo bar ]} to create abstract variables
	(see page~\pageref{ssec:introabstract}).
\item Tactic \ssrC{abstract:} to assign an abstract variable
	(see page~\pageref{ssec:abstract}).\\
  \ssrC{have [: blurb ] @i : 'I\_n by apply: (Sub m); abstract: blurb; auto.}\\
  \ssrC{have [: blurb ] i : 'I\_n := Sub m  blurb; first by auto.}

\end{itemize}

\fi
