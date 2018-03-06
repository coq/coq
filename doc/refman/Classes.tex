\def\Haskell{\textsc{Haskell}\xspace}
\def\eol{\setlength\parskip{0pt}\par}
\def\indent#1{\noindent\kern#1}
\def\cst#1{\textsf{#1}}

\newcommand\tele[1]{\overrightarrow{#1}}

\achapter{\protect{Type Classes}}
%HEVEA\cutname{type-classes.html}
\aauthor{Matthieu Sozeau}
\label{typeclasses}

This chapter presents a quick reference of the commands related to type
classes. For an actual introduction to type classes, there is a
description of the system \cite{sozeau08} and the literature on type
classes in \Haskell which also applies.

\asection{Class and Instance declarations}
\label{ClassesInstances}

The syntax for class and instance declarations is the same as
record syntax of \Coq:
\def\kw{\texttt}
\def\classid{\texttt}

\begin{center}
\[\begin{array}{l}
\kw{Class}~\classid{Id}~(\alpha_1 : \tau_1) \cdots (\alpha_n : \tau_n) 
[: \sort] := \{\\
\begin{array}{p{0em}lcl}
  & \cst{f}_1 & : & \type_1 ; \\
  & \vdots & &  \\
  & \cst{f}_m & : & \type_m \}.
\end{array}\end{array}\]
\end{center}
\begin{center}
\[\begin{array}{l}
\kw{Instance}~\ident~:~\classid{Id}~\term_1 \cdots \term_n := \{\\
\begin{array}{p{0em}lcl}
  & \cst{f}_1 & := & \term_{f_1} ; \\
  & \vdots & &  \\
  & \cst{f}_m & := & \term_{f_m} \}.
\end{array}\end{array}\]
\end{center}
\begin{coq_eval}
  Reset Initial.
  Generalizable All Variables.
\end{coq_eval}

The $\tele{\alpha_i : \tau_i}$ variables are called the \emph{parameters}
of the class and the $\tele{f_k : \type_k}$ are called the
\emph{methods}. Each class definition gives rise to a corresponding
record declaration and each instance is a regular definition whose name
is given by $\ident$ and type is an instantiation of the record type.

We'll use the following example class in the rest of the chapter:

\begin{coq_example*}
Class EqDec (A : Type) := {
  eqb : A -> A -> bool ;
  eqb_leibniz : forall x y, eqb x y = true -> x = y }.
\end{coq_example*}

This class implements a boolean equality test which is compatible with
Leibniz equality on some type. An example implementation is:

\begin{coq_example*}
Instance unit_EqDec : EqDec unit :=
{ eqb x y := true ;
  eqb_leibniz x y H := 
    match x, y return x = y with tt, tt => eq_refl tt end }.
\end{coq_example*}

If one does not give all the members in the \texttt{Instance}
declaration, Coq enters the proof-mode and the user is asked to build
inhabitants of the remaining fields, e.g.:

\begin{coq_example*}
Instance eq_bool : EqDec bool :=
{ eqb x y := if x then y else negb y }.
\end{coq_example*}
\begin{coq_example}
Proof. intros x y H.
  destruct x ; destruct y ; (discriminate || reflexivity). 
Defined.
\end{coq_example}

One has to take care that the transparency of every field is determined
by the transparency of the \texttt{Instance} proof. One can use
alternatively the \texttt{Program} \texttt{Instance} \comindex{Program Instance} variant which has
richer facilities for dealing with obligations.

\asection{Binding classes}

Once a type class is declared, one can use it in class binders:
\begin{coq_example}
Definition neqb {A} {eqa : EqDec A} (x y : A) := negb (eqb x y).
\end{coq_example}

When one calls a class method, a constraint is generated that is
satisfied only in contexts where the appropriate instances can be
found. In the example above, a constraint \texttt{EqDec A} is generated and
satisfied by \texttt{{eqa : EqDec A}}. In case no satisfying constraint can be
found, an error is raised:

\begin{coq_example}
Fail Definition neqb' (A : Type) (x y : A) := negb (eqb x y).
\end{coq_example}

The algorithm used to solve constraints is a variant of the eauto tactic
that does proof search with a set of lemmas (the instances). It will use
local hypotheses as well as declared lemmas in the
\texttt{typeclass\_instances} database. Hence the example can also be
written:

\begin{coq_example}
Definition neqb' A (eqa : EqDec A) (x y : A) := negb (eqb x y).
\end{coq_example}

However, the generalizing binders should be used instead as they have
particular support for type classes:
\begin{itemize}
\item They automatically set the maximally implicit status for type
  class arguments, making derived functions as easy to use as class
  methods. In the example above, \texttt{A} and \texttt{eqa} should be
  set maximally implicit.
\item They support implicit quantification on partially applied type
  classes (\S \ref{implicit-generalization}).
  Any argument not given as part of a type class binder will be
  automatically generalized.
\item They also support implicit quantification on superclasses
  (\S \ref{classes:superclasses})
\end{itemize}

Following the previous example, one can write:
\begin{coq_example}
Definition neqb_impl `{eqa : EqDec A} (x y : A) := negb (eqb x y).
\end{coq_example}

Here \texttt{A} is implicitly generalized, and the resulting function
is equivalent to the one above.

\asection{Parameterized Instances}

One can declare parameterized instances as in \Haskell simply by giving
the constraints as a binding context before the instance, e.g.:

\begin{coq_example}
Instance prod_eqb `(EA : EqDec A, EB : EqDec B) : EqDec (A * B) :=
{ eqb x y := match x, y with
  | (la, ra), (lb, rb) => andb (eqb la lb) (eqb ra rb)
  end }.
\end{coq_example}
\begin{coq_eval}
Admitted.
\end{coq_eval}

These instances are used just as well as lemmas in the instance hint database.

\asection{Sections and contexts}
\label{SectionContext}
To ease the parametrization of developments by type classes, we provide
a new way to introduce variables into section contexts, compatible with 
the implicit argument mechanism. 
The new command works similarly to the \texttt{Variables} vernacular
(see \ref{Variable}), except it accepts any binding context as argument.
For example:

\begin{coq_example}
Section EqDec_defs.
  Context `{EA : EqDec A}.
\end{coq_example}

\begin{coq_example*}
  Global Instance option_eqb : EqDec (option A) :=
  { eqb x y := match x, y with
    | Some x, Some y => eqb x y
    | None, None => true
    | _, _ => false
    end }.
\end{coq_example*}
\begin{coq_eval}
Proof.
intros x y ; destruct x ; destruct y ; intros H ; 
try discriminate ; try apply eqb_leibniz in H ;
subst ; auto. 
Defined.
\end{coq_eval}

\begin{coq_example}
End EqDec_defs.
About option_eqb.
\end{coq_example}

Here the \texttt{Global} modifier redeclares the instance at the end of 
the section, once it has been generalized by the context variables it uses.

\asection{Building hierarchies}

\subsection{Superclasses}
\label{classes:superclasses}
One can also parameterize classes by other classes, generating a
hierarchy of classes and superclasses. In the same way, we give the
superclasses as a binding context:

\begin{coq_example*}
Class Ord `(E : EqDec A) :=
  { le : A -> A -> bool }.
\end{coq_example*}

Contrary to \Haskell, we have no special syntax for superclasses, but
this declaration is morally equivalent to:
\begin{verbatim}
Class `(E : EqDec A) => Ord A :=
  { le : A -> A -> bool }.
\end{verbatim}

This declaration means that any instance of the \texttt{Ord} class must
have an instance of \texttt{EqDec}. The parameters of the subclass contain
at least all the parameters of its superclasses in their order of
appearance (here \texttt{A} is the only one).
As we have seen, \texttt{Ord} is encoded as a record type with two parameters:
a type \texttt{A} and an \texttt{E} of type \texttt{EqDec A}. However, one can
still use it as if it had a single parameter inside generalizing binders: the
generalization of superclasses will be done automatically. 
\begin{coq_example*}
Definition le_eqb `{Ord A} (x y : A) := andb (le x y) (le y x).
\end{coq_example*}

In some cases, to be able to specify sharing of structures, one may want to give
explicitly the superclasses. It is is possible to do it directly in regular
binders, and using the \texttt{!} modifier in class binders. For
example:
\begin{coq_example*}
Definition lt `{eqa : EqDec A, ! Ord eqa} (x y : A) := 
  andb (le x y) (neqb x y).
\end{coq_example*}

The \texttt{!} modifier switches the way a binder is parsed back to the
regular interpretation of Coq. In particular, it uses the implicit
arguments mechanism if available, as shown in the example.

\subsection{Substructures}

Substructures are components of a class which are instances of a class
themselves. They often arise when using classes for logical properties,
e.g.:

\begin{coq_eval}
Require Import Relations.
\end{coq_eval}
\begin{coq_example*}
Class Reflexive (A : Type) (R : relation A) :=
  reflexivity : forall x, R x x.
Class Transitive (A : Type) (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.
\end{coq_example*}

This declares singleton classes for reflexive and transitive relations,
(see \ref{SingletonClass} for an explanation).
These may be used as part of other classes:

\begin{coq_example*}
Class PreOrder (A : Type) (R : relation A) :=
{ PreOrder_Reflexive :> Reflexive A R ;
  PreOrder_Transitive :> Transitive A R }.
\end{coq_example*}

The syntax \texttt{:>} indicates that each \texttt{PreOrder} can be seen
as a \texttt{Reflexive} relation. So each time a reflexive relation is
needed, a preorder can be used instead. This is very similar to the
coercion mechanism of \texttt{Structure} declarations.
The implementation simply declares each projection as an instance. 

One can also declare existing objects or structure
projections using the \texttt{Existing Instance} command to achieve the 
same effect.

\section{Summary of the commands
\label{TypeClassCommands}}

\subsection{\tt Class {\ident} {\binder$_1$ \ldots~\binder$_n$} 
  : \sort := \{ field$_1$ ; \ldots ; field$_k$ \}.}
\comindex{Class}
\label{Class}

The \texttt{Class} command is used to declare a type class with
parameters {\binder$_1$} to {\binder$_n$} and fields {\tt field$_1$} to
{\tt field$_k$}.

\begin{Variants}
\item \label{SingletonClass} {\tt Class {\ident} {\binder$_1$ \ldots \binder$_n$} 
    : \sort := \ident$_1$ : \type$_1$.}
  This variant declares a \emph{singleton} class whose only method is
  {\tt \ident$_1$}. This singleton class is a so-called definitional
  class, represented simply as a definition 
  {\tt {\ident} \binder$_1$ \ldots \binder$_n$ := \type$_1$} and whose
  instances are themselves objects of this type. Definitional classes
  are not wrapped inside records, and the trivial projection of an
  instance of such a class is convertible to the instance itself. This can
  be useful to make instances of existing objects easily and to reduce 
  proof size by not inserting useless projections. The class
  constant itself is declared rigid during resolution so that the class 
  abstraction is maintained.  

\item \label{ExistingClass} {\tt Existing Class {\ident}.\comindex{Existing Class}}
  This variant declares a class a posteriori from a constant or
  inductive definition. No methods or instances are defined.
\end{Variants}

\subsection{\tt Instance {\ident} {\binder$_1$ \ldots \binder$_n$} :
  {Class} {t$_1$ \ldots t$_n$} [| \textit{priority}]
  := \{ field$_1$ := b$_1$ ; \ldots ; field$_i$ := b$_i$ \}}
\comindex{Instance}
\label{Instance}

The \texttt{Instance} command is used to declare a type class instance
named {\ident} of the class \emph{Class} with parameters {t$_1$} to {t$_n$} and
fields {\tt b$_1$} to {\tt b$_i$}, where each field must be a declared
field of the class. Missing fields must be filled in interactive proof mode.

An arbitrary context of the form {\tt \binder$_1$ \ldots \binder$_n$}
can be put after the name of the instance and before the colon to
declare a parameterized instance.
An optional \textit{priority} can be declared, 0 being the highest
priority as for auto hints. If the priority is not specified, it defaults to
$n$, the number of binders of the instance.

\begin{Variants}
\item {\tt Instance {\ident} {\binder$_1$ \ldots \binder$_n$} :
    forall {\binder$_{n+1}$ \ldots \binder$_m$},
    {Class} {t$_1$ \ldots t$_n$} [| \textit{priority}] := \term} 
  This syntax is used for declaration of singleton class instances or
  for directly giving an explicit term of type
  {\tt forall {\binder$_{n+1}$ \ldots \binder$_m$}, {Class} {t$_1$ \ldots t$_n$}}.
  One need not even mention the unique field name for singleton classes.

\item {\tt Global Instance} One can use the \texttt{Global} modifier on
  instances declared in a section so that their generalization is automatically
  redeclared after the section is closed.

\item {\tt Program Instance} \comindex{Program Instance}
  Switches the type-checking to \Program~(chapter \ref{Program})
  and uses the obligation mechanism to manage missing fields.

\item {\tt Declare Instance} \comindex{Declare Instance}
  In a {\tt Module Type}, this command states that a corresponding
  concrete instance should exist in any implementation of this
  {\tt Module Type}. This is similar to the distinction between
  {\tt Parameter} vs. {\tt Definition}, or between {\tt Declare Module}
  and {\tt Module}.

\end{Variants}

Besides the {\tt Class} and {\tt Instance} vernacular commands, there
are a few other commands related to type classes.

\subsection{\tt Existing Instance {\ident} [| \textit{priority}]}
\comindex{Existing Instance}
\label{ExistingInstance}

This commands adds an arbitrary constant whose type ends with an applied
type class to the instance database with an optional priority. It can be used
for redeclaring instances at the end of sections, or declaring structure
projections as instances. This is almost equivalent to {\tt Hint Resolve
{\ident} : typeclass\_instances}.

\begin{Variants}
\item {\tt Existing Instances {\ident}$_1$ \ldots {\ident}$_n$
  [| \textit{priority}]}
  \comindex{Existing Instances}
  With this command, several existing instances can be declared at once.
\end{Variants}

\subsection{\tt Context {\binder$_1$ \ldots \binder$_n$}}
\comindex{Context}
\label{Context}

Declares variables according to the given binding context, which might
use implicit generalization (see \ref{SectionContext}).

\asubsection{\tt typeclasses eauto}
\tacindex{typeclasses eauto}
\label{typeclasseseauto}

The {\tt typeclasses eauto} tactic uses a different resolution engine
than {\tt eauto} and {\tt auto}. The main differences are the following:
\begin{itemize}
\item Contrary to {\tt eauto} and {\tt auto}, the resolution is done
  entirely in the new proof engine (as of Coq v8.6), meaning that
  backtracking is available among dependent subgoals, and shelving goals
  is supported. {\tt typeclasses eauto} is a multi-goal tactic.
  It analyses the dependencies between subgoals to avoid
  backtracking on subgoals that are entirely independent.
\item When called with no arguments, {\tt typeclasses eauto} uses the
  {\tt typeclass\_instances} database by default (instead of {\tt
    core}).
  Dependent subgoals are automatically shelved, and shelved
  goals can remain after resolution ends (following the behavior of
  \Coq{} 8.5).

  \emph{Note: } As of Coq 8.6, {\tt all:once (typeclasses eauto)}
  faithfully mimicks what happens during typeclass resolution when it is
  called during refinement/type-inference, except that \emph{only}
  declared class subgoals are considered at the start of resolution
  during type inference, while ``all'' can select non-class subgoals as
  well. It might move to {\tt all:typeclasses eauto} in future versions
  when the refinement engine will be able to backtrack.
\item When called with specific databases (e.g. {\tt with}), {\tt
    typeclasses eauto} allows shelved goals to remain at any point
  during search and treat typeclasses goals like any other.
\item The transparency information of databases is used consistently for
  all hints declared in them. It is always used when calling the unifier.
  When considering the local hypotheses, we use the transparent
  state of the first hint database given. Using an empty database
  (created with {\tt Create HintDb} for example) with 
  unfoldable variables and constants as the first argument of
  typeclasses eauto hence makes resolution with the local hypotheses use
  full conversion during unification.
\end{itemize}

\begin{Variants}
\item \label{depth} {\tt typeclasses eauto \zeroone{\num}}
  \emph{Warning:} The semantics for the limit {\num} is different than
  for {\tt auto}. By default, if no limit is given the search is
  unbounded. Contrary to {\tt auto}, introduction steps ({\tt intro})
  are counted, which might result in larger limits being necessary
  when searching with {\tt typeclasses eauto} than {\tt auto}.
  
\item \label{with} {\tt typeclasses eauto with {\ident}$_1$ \ldots {\ident}$_n$}.
  This variant runs resolution with the given hint databases. It treats
  typeclass subgoals the same as other subgoals (no shelving of
  non-typeclass goals in particular).
\end{Variants}

\asubsection{\tt autoapply {\term} with {\ident}}
\tacindex{autoapply}

The tactic {\tt autoapply} applies a term using the transparency
information of the hint database {\ident}, and does \emph{no} typeclass
resolution. This can be used in {\tt Hint Extern}'s for typeclass
instances (in hint db {\tt typeclass\_instances}) to
allow backtracking on the typeclass subgoals created by the lemma
application, rather than doing type class resolution locally at the hint
application time.

\subsection{\tt Typeclasses Transparent, Opaque {\ident$_1$ \ldots \ident$_n$}}
\comindex{Typeclasses Transparent}
\comindex{Typeclasses Opaque}
\label{TypeclassesTransparency}

This commands defines the transparency of {\ident$_1$ \ldots \ident$_n$} 
during type class resolution. It is useful when some constants prevent some
unifications and make resolution fail. It is also useful to declare
constants which should never be unfolded during proof-search, like
fixpoints or anything which does not look like an abbreviation. This can
additionally speed up proof search as the typeclass map can be indexed
by such rigid constants (see \ref{HintTransparency}).
By default, all constants and local variables are considered transparent.
One should take care not to make opaque any constant that is used to
abbreviate a type, like {\tt relation A := A -> A -> Prop}.

This is equivalent to {\tt Hint Transparent,Opaque} {\ident} {\tt: typeclass\_instances}.

\subsection{\tt Set Typeclasses Axioms Are Instances}
\optindex{Typeclasses Axioms Are Instances}

This option (off by default since 8.8) automatically declares axioms
whose type is a typeclass at declaration time as instances of that
class.

\subsection{\tt Set Typeclasses Dependency Order}
\optindex{Typeclasses Dependency Order}

This option (on by default since 8.6) respects the dependency order between
subgoals, meaning that subgoals which are depended on by other subgoals
come first, while the non-dependent subgoals were put before the
dependent ones previously (Coq v8.5 and below). This can result in quite
different performance behaviors of proof search.

\subsection{\tt Set Typeclasses Filtered Unification}
\optindex{Typeclasses Filtered Unification}

This option, available since Coq 8.6 and off by default, switches the
hint application procedure to a filter-then-unify strategy. To apply a
hint, we first check that the goal \emph{matches} syntactically the
inferred or specified pattern of the hint, and only then try to
\emph{unify} the goal with the conclusion of the hint. This can
drastically improve performance by calling unification less often,
matching syntactic patterns being very quick. This also provides more
control on the triggering of instances.  For example, forcing a constant
to explicitely appear in the pattern will make it never apply on a goal
where there is a hole in that place.

\subsection{\tt Set Typeclasses Limit Intros}
\optindex{Typeclasses Limit Intros}

This option (on by default) controls the ability to
apply hints while avoiding (functional) eta-expansions in the generated
proof term. It does so by allowing hints that conclude in a product to
apply to a goal with a matching product directly, avoiding an
introduction. \emph{Warning:} this can be expensive as it requires
rebuilding hint clauses dynamically, and does not benefit from the
invertibility status of the product introduction rule, resulting in
potentially more expensive proof-search (i.e. more useless
backtracking).

\subsection{\tt Set Typeclass Resolution For Conversion}
\optindex{Typeclass Resolution For Conversion}

This option (on by default) controls the use of typeclass resolution
when a unification problem cannot be solved during
elaboration/type-inference. With this option on, when a unification
fails, typeclass resolution is tried before launching unification once again.

\subsection{\tt Set Typeclasses Strict Resolution}
\optindex{Typeclasses Strict Resolution}

Typeclass declarations introduced when this option is set have a
stricter resolution behavior (the option is off by default). When
looking for unifications of a goal with an instance of this class, we
``freeze'' all the existentials appearing in the goals, meaning that
they are considered rigid during unification and cannot be instantiated.

\subsection{\tt Set Typeclasses Unique Solutions}
\optindex{Typeclasses Unique Solutions}

When a typeclass resolution is launched we ensure that it has a single
solution or fail. This ensures that the resolution is canonical, but can
make proof search much more expensive.

\subsection{\tt Set Typeclasses Unique Instances}
\optindex{Typeclasses Unique Instances}

Typeclass declarations introduced when this option is set have a
more efficient resolution behavior (the option is off by default). When
a solution to the typeclass goal of this class is found, we never
backtrack on it, assuming that it is canonical.

\subsection{\tt Typeclasses eauto := [debug] [(dfs) | (bfs)] [\emph{depth}]}
\comindex{Typeclasses eauto}
\label{TypeclassesEauto}

This command allows more global customization of the type class
resolution tactic.
The semantics of the options are:
\begin{itemize}
\item {\tt debug} In debug mode, the trace of successfully applied
  tactics is printed.
\item {\tt dfs, bfs} This sets the search strategy to depth-first search
  (the default) or breadth-first search.
\item {\emph{depth}} This sets the depth limit of the search.
\end{itemize}

\subsection{\tt Set Typeclasses Debug [Verbosity {\num}]}
\optindex{Typeclasses Debug}
\optindex{Typeclasses Debug Verbosity}

These options allow to see the resolution steps of typeclasses that are
performed during search. The {\tt Debug} option is synonymous to 
{\tt Debug Verbosity 1}, and {\tt Debug Verbosity 2} provides more
information (tried tactics, shelving of goals, etc\ldots).

\subsection{\tt Set Refine Instance Mode}
\optindex{Refine Instance Mode}

The option {\tt Refine Instance Mode} allows to switch the behavior of instance
declarations made through the {\tt Instance} command.
\begin{itemize}
\item When it is on (the default), instances that have unsolved holes in their
proof-term silently open the proof mode with the remaining obligations to prove.
\item When it is off, they fail with an error instead.
\end{itemize}

%%% Local Variables: 
%%% mode: latex
%%% TeX-master: "Reference-Manual"
%%% End: 
