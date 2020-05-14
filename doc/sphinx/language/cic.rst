Typing rules
====================================

The underlying formal language of |Coq| is a *Calculus of Inductive
Constructions* (|Cic|) whose inference rules are presented in this
chapter. The history of this formalism as well as pointers to related
work are provided in a separate chapter; see *Credits*.


.. _The-terms:

The terms
-------------

The expressions of the |Cic| are *terms* and all terms have a *type*.
There are types for functions (or programs), there are atomic types
(especially datatypes)... but also types for proofs and types for the
types themselves. Especially, any object handled in the formalism must
belong to a type. For instance, universal quantification is relative
to a type and takes the form “*for all x of type* :math:`T`, :math:`P`”. The expression
“:math:`x` *of type* :math:`T`” is written “:math:`x:T`”. Informally, “:math:`x:T`” can be thought as
“:math:`x` *belongs to* :math:`T`”.

Terms are built from sorts, variables, constants, abstractions,
applications, local definitions, and products. From a syntactic point
of view, types cannot be distinguished from terms, except that they
cannot start by an abstraction or a constructor. More precisely the
language of the *Calculus of Inductive Constructions* is built from
the following rules.


#. the sorts :math:`\SProp`, :math:`\Prop`, :math:`\Set`, :math:`\Type(i)` are terms.
#. variables, hereafter ranged over by letters :math:`x`, :math:`y`, etc., are terms
#. constants, hereafter ranged over by letters :math:`c`, :math:`d`, etc., are terms.
#. if :math:`x` is a variable and :math:`T`, :math:`U` are terms then
   :math:`∀ x:T,~U` (:g:`forall x:T, U`   in |Coq| concrete syntax) is a term.
   If :math:`x` occurs in :math:`U`, :math:`∀ x:T,~U` reads as
   “for all :math:`x` of type :math:`T`, :math:`U`”.
   As :math:`U` depends on :math:`x`, one says that :math:`∀ x:T,~U` is
   a *dependent product*. If :math:`x` does not occur in :math:`U` then
   :math:`∀ x:T,~U` reads as
   “if :math:`T` then :math:`U`”. A *non dependent product* can be
   written: :math:`T \rightarrow U`.
#. if :math:`x` is a variable and :math:`T`, :math:`u` are terms then
   :math:`λ x:T .~u` (:g:`fun x:T => u`
   in |Coq| concrete syntax) is a term. This is a notation for the
   λ-abstraction of λ-calculus :cite:`Bar81`. The term :math:`λ x:T .~u` is a function
   which maps elements of :math:`T` to the expression :math:`u`.
#. if :math:`t` and :math:`u` are terms then :math:`(t~u)` is a term
   (:g:`t u` in |Coq| concrete
   syntax). The term :math:`(t~u)` reads as “:math:`t` applied to :math:`u`”.
#. if :math:`x` is a variable, and :math:`t`, :math:`T` and :math:`u` are
   terms then :math:`\letin{x}{t:T}{u}` is
   a term which denotes the term :math:`u` where the variable :math:`x` is locally bound
   to :math:`t` of type :math:`T`. This stands for the common “let-in” construction of
   functional programs such as ML or Scheme.



.. _Free-variables:

**Free variables.**
The notion of free variables is defined as usual. In the expressions
:math:`λx:T.~U` and :math:`∀ x:T,~U` the occurrences of :math:`x` in :math:`U` are bound.


.. _Substitution:

**Substitution.**
The notion of substituting a term :math:`t` to free occurrences of a variable
:math:`x` in a term :math:`u` is defined as usual. The resulting term is written
:math:`\subst{u}{x}{t}`.


.. _The-logical-vs-programming-readings:

**The logical vs programming readings.**
The constructions of the |Cic| can be used to express both logical and
programming notions, accordingly to the Curry-Howard correspondence
between proofs and programs, and between propositions and types
:cite:`Cur58,How80,Bru72`.

For instance, let us assume that :math:`\nat` is the type of natural numbers
with zero element written :math:`0` and that :g:`True` is the always true
proposition. Then :math:`→` is used both to denote :math:`\nat→\nat` which is the type
of functions from :math:`\nat` to :math:`\nat`, to denote True→True which is an
implicative proposition, to denote :math:`\nat →\Prop` which is the type of
unary predicates over the natural numbers, etc.

Let us assume that ``mult`` is a function of type :math:`\nat→\nat→\nat` and ``eqnat`` a
predicate of type :math:`\nat→\nat→ \Prop`. The λ-abstraction can serve to build
“ordinary” functions as in :math:`λ x:\nat.~(\kw{mult}~x~x)` (i.e.
:g:`fun x:nat => mult x x`
in |Coq| notation) but may build also predicates over the natural
numbers. For instance :math:`λ x:\nat.~(\kw{eqnat}~x~0)`
(i.e. :g:`fun x:nat => eqnat x 0`
in |Coq| notation) will represent the predicate of one variable :math:`x` which
asserts the equality of :math:`x` with :math:`0`. This predicate has type
:math:`\nat → \Prop`
and it can be applied to any expression of type :math:`\nat`, say :math:`t`, to give an
object :math:`P~t` of type :math:`\Prop`, namely a proposition.

Furthermore :g:`forall x:nat, P x` will represent the type of functions
which associate to each natural number :math:`n` an object of type :math:`(P~n)` and
consequently represent the type of proofs of the formula “:math:`∀ x.~P(x)`”.


.. _Typing-rules:

Typing rules
----------------

As objects of type theory, terms are subjected to *type discipline*.
The well typing of a term depends on a global environment and a local
context.


.. _Local-context:

**Local context.**
A *local context* is an ordered list of *local declarations* of names
which we call *variables*. The declaration of some variable :math:`x` is
either a *local assumption*, written :math:`x:T` (:math:`T` is a type) or a *local
definition*, written :math:`x:=t:T`. We use brackets to write local contexts.
A typical example is :math:`[x:T;~y:=u:U;~z:V]`. Notice that the variables
declared in a local context must be distinct. If :math:`Γ` is a local context
that declares some :math:`x`, we
write :math:`x ∈ Γ`. By writing :math:`(x:T) ∈ Γ` we mean that either :math:`x:T` is an
assumption in :math:`Γ` or that there exists some :math:`t` such that :math:`x:=t:T` is a
definition in :math:`Γ`. If :math:`Γ` defines some :math:`x:=t:T`, we also write :math:`(x:=t:T) ∈ Γ`.
For the rest of the chapter, :math:`Γ::(y:T)` denotes the local context :math:`Γ`
enriched with the local assumption :math:`y:T`. Similarly, :math:`Γ::(y:=t:T)` denotes
the local context :math:`Γ` enriched with the local definition :math:`(y:=t:T)`. The
notation :math:`[]` denotes the empty local context. By :math:`Γ_1 ; Γ_2` we mean
concatenation of the local context :math:`Γ_1` and the local context :math:`Γ_2`.


.. _Global-environment:

**Global environment.**
A *global environment* is an ordered list of *global declarations*.
Global declarations are either *global assumptions* or *global
definitions*, but also declarations of inductive objects. Inductive
objects themselves declare both inductive or coinductive types and
constructors (see Section :ref:`inductive-definitions`).

A *global assumption* will be represented in the global environment as
:math:`(c:T)` which assumes the name :math:`c` to be of some type :math:`T`. A *global
definition* will be represented in the global environment as :math:`c:=t:T`
which defines the name :math:`c` to have value :math:`t` and type :math:`T`. We shall call
such names *constants*. For the rest of the chapter, the :math:`E;~c:T` denotes
the global environment :math:`E` enriched with the global assumption :math:`c:T`.
Similarly, :math:`E;~c:=t:T` denotes the global environment :math:`E` enriched with the
global definition :math:`(c:=t:T)`.

The rules for inductive definitions (see Section
:ref:`inductive-definitions`) have to be considered as assumption
rules to which the following definitions apply: if the name :math:`c`
is declared in :math:`E`, we write :math:`c ∈ E` and if :math:`c:T` or
:math:`c:=t:T` is declared in :math:`E`, we write :math:`(c : T) ∈ E`.


.. _Typing-rules2:

**Typing rules.**
In the following, we define simultaneously two judgments. The first
one :math:`\WTEG{t}{T}` means the term :math:`t` is well-typed and has type :math:`T` in the
global environment :math:`E` and local context :math:`Γ`. The second judgment :math:`\WFE{Γ}`
means that the global environment :math:`E` is well-formed and the local
context :math:`Γ` is a valid local context in this global environment.

A term :math:`t` is well typed in a global environment :math:`E` iff
there exists a local context :math:`\Gamma` and a term :math:`T` such
that the judgment :math:`\WTEG{t}{T}` can be derived from the
following rules.

.. inference:: W-Empty

   ---------
   \WF{[]}{}

.. inference:: W-Local-Assum

   \WTEG{T}{s}
   s \in \Sort
   x \not\in \Gamma % \cup E
   -------------------------
   \WFE{\Gamma::(x:T)}

.. inference:: W-Local-Def

   \WTEG{t}{T}
   x \not\in \Gamma % \cup E
   -------------------------
   \WFE{\Gamma::(x:=t:T)}

.. inference:: W-Global-Assum

   \WTE{}{T}{s}
   s \in \Sort
   c \notin E
   ------------
   \WF{E;~c:T}{}

.. inference:: W-Global-Def

   \WTE{}{t}{T}
   c \notin E
   ---------------
   \WF{E;~c:=t:T}{}

.. inference:: Ax-SProp

   \WFE{\Gamma}
   ----------------------
   \WTEG{\SProp}{\Type(1)}

.. inference:: Ax-Prop

   \WFE{\Gamma}
   ----------------------
   \WTEG{\Prop}{\Type(1)}

.. inference:: Ax-Set

   \WFE{\Gamma}
   ---------------------
   \WTEG{\Set}{\Type(1)}

.. inference:: Ax-Type

   \WFE{\Gamma}
   ---------------------------
   \WTEG{\Type(i)}{\Type(i+1)}

.. inference:: Var

   \WFE{\Gamma}
   (x:T) \in \Gamma~~\mbox{or}~~(x:=t:T) \in \Gamma~\mbox{for some $t$}
   --------------------------------------------------------------------
   \WTEG{x}{T}

.. inference:: Const

   \WFE{\Gamma}
   (c:T) \in E~~\mbox{or}~~(c:=t:T) \in E~\mbox{for some $t$}
   ----------------------------------------------------------
   \WTEG{c}{T}

.. inference:: Prod-SProp

   \WTEG{T}{s}
   s \in {\Sort}
   \WTE{\Gamma::(x:T)}{U}{\SProp}
   -----------------------------
   \WTEG{\forall~x:T,U}{\SProp}

.. inference:: Prod-Prop

   \WTEG{T}{s}
   s \in \Sort
   \WTE{\Gamma::(x:T)}{U}{\Prop}
   -----------------------------
   \WTEG{∀ x:T,~U}{\Prop}

.. inference:: Prod-Set

   \WTEG{T}{s}
   s \in \{\SProp, \Prop, \Set\}
   \WTE{\Gamma::(x:T)}{U}{\Set}
   ----------------------------
   \WTEG{∀ x:T,~U}{\Set}

.. inference:: Prod-Type

   \WTEG{T}{s}
   s \in \{\SProp, \Type{i}\}
   \WTE{\Gamma::(x:T)}{U}{\Type(i)}
   --------------------------------
   \WTEG{∀ x:T,~U}{\Type(i)}

.. inference:: Lam

   \WTEG{∀ x:T,~U}{s}
   \WTE{\Gamma::(x:T)}{t}{U}
   ------------------------------------
   \WTEG{λ x:T\mto t}{∀ x:T,~U}

.. inference:: App

   \WTEG{t}{∀ x:U,~T}
   \WTEG{u}{U}
   ------------------------------
   \WTEG{(t\ u)}{\subst{T}{x}{u}}

.. inference:: Let

   \WTEG{t}{T}
   \WTE{\Gamma::(x:=t:T)}{u}{U}
   -----------------------------------------
   \WTEG{\letin{x}{t:T}{u}}{\subst{U}{x}{t}}



.. note::

   **Prod-Prop** and **Prod-Set** typing-rules make sense if we consider the
   semantic difference between :math:`\Prop` and :math:`\Set`:

   + All values of a type that has a sort :math:`\Set` are extractable.
   + No values of a type that has a sort :math:`\Prop` are extractable.



.. note::
   We may have :math:`\letin{x}{t:T}{u}` well-typed without having
   :math:`((λ x:T.~u)~t)` well-typed (where :math:`T` is a type of
   :math:`t`). This is because the value :math:`t` associated to
   :math:`x` may be used in a conversion rule
   (see Section :ref:`Conversion-rules`).

.. _subtyping-rules:

Subtyping rules
-------------------

At the moment, we did not take into account one rule between universes
which says that any term in a universe of index :math:`i` is also a term in
the universe of index :math:`i+1` (this is the *cumulativity* rule of |Cic|).
This property extends the equivalence relation of convertibility into
a *subtyping* relation inductively defined by:


#. if :math:`E[Γ] ⊢ t =_{βδιζη} u` then :math:`E[Γ] ⊢ t ≤_{βδιζη} u`,
#. if :math:`i ≤ j` then :math:`E[Γ] ⊢ \Type(i) ≤_{βδιζη} \Type(j)`,
#. for any :math:`i`, :math:`E[Γ] ⊢ \Set ≤_{βδιζη} \Type(i)`,
#. :math:`E[Γ] ⊢ \Prop ≤_{βδιζη} \Set`, hence, by transitivity,
   :math:`E[Γ] ⊢ \Prop ≤_{βδιζη} \Type(i)`, for any :math:`i`
   (note: :math:`\SProp` is not related by cumulativity to any other term)
#. if :math:`E[Γ] ⊢ T =_{βδιζη} U` and
   :math:`E[Γ::(x:T)] ⊢ T' ≤_{βδιζη} U'` then
   :math:`E[Γ] ⊢ ∀x:T,~T′ ≤_{βδιζη} ∀ x:U,~U′`.
#. if :math:`\ind{p}{Γ_I}{Γ_C}` is a universe polymorphic and cumulative
   (see Chapter :ref:`polymorphicuniverses`) inductive type (see below)
   and
   :math:`(t : ∀Γ_P ,∀Γ_{\mathit{Arr}(t)}, S)∈Γ_I`
   and
   :math:`(t' : ∀Γ_P' ,∀Γ_{\mathit{Arr}(t)}', S')∈Γ_I`
   are two different instances of *the same* inductive type (differing only in
   universe levels) with constructors

   .. math::
      [c_1 : ∀Γ_P ,∀ T_{1,1} … T_{1,n_1} ,~t~v_{1,1} … v_{1,m} ;~…;~
       c_k : ∀Γ_P ,∀ T_{k,1} … T_{k,n_k} ,~t~v_{k,1} … v_{k,m} ]

   and

   .. math::
      [c_1 : ∀Γ_P' ,∀ T_{1,1}' … T_{1,n_1}' ,~t'~v_{1,1}' … v_{1,m}' ;~…;~
       c_k : ∀Γ_P' ,∀ T_{k,1}' … T_{k,n_k}' ,~t'~v_{k,1}' … v_{k,m}' ]

   respectively then

   .. math::
      E[Γ] ⊢ t~w_1 … w_m ≤_{βδιζη} t'~w_1' … w_m'

   (notice that :math:`t` and :math:`t'` are both
   fully applied, i.e., they have a sort as a type) if

   .. math::
      E[Γ] ⊢ w_i =_{βδιζη} w_i'

   for :math:`1 ≤ i ≤ m` and we have


   .. math::
      E[Γ] ⊢ T_{i,j} ≤_{βδιζη} T_{i,j}'

   and

   .. math::
      E[Γ] ⊢ A_i ≤_{βδιζη} A_i'

   where :math:`Γ_{\mathit{Arr}(t)} = [a_1 : A_1 ;~ … ;~a_l : A_l ]` and
   :math:`Γ_{\mathit{Arr}(t)}' = [a_1 : A_1';~ … ;~a_l : A_l']`.


The conversion rule up to subtyping is now exactly:

.. inference:: Conv

   E[Γ] ⊢ U : s
   E[Γ] ⊢ t : T
   E[Γ] ⊢ T ≤_{βδιζη} U
   --------------
   E[Γ] ⊢ t : U


.. _Normal-form:

**Normal form**. A term which cannot be any more reduced is said to be in *normal
form*. There are several ways (or strategies) to apply the reduction
rules. Among them, we have to mention the *head reduction* which will
play an important role (see Chapter :ref:`tactics`). Any term :math:`t` can be written as
:math:`λ x_1 :T_1 .~… λ x_k :T_k .~(t_0~t_1 … t_n )` where :math:`t_0` is not an
application. We say then that :math:`t_0` is the *head of* :math:`t`. If we assume
that :math:`t_0` is :math:`λ x:T.~u_0` then one step of β-head reduction of :math:`t` is:

.. math::
   λ x_1 :T_1 .~… λ x_k :T_k .~(λ x:T.~u_0~t_1 … t_n ) ~\triangleright~
   λ (x_1 :T_1 )…(x_k :T_k ).~(\subst{u_0}{x}{t_1}~t_2 … t_n )

Iterating the process of head reduction until the head of the reduced
term is no more an abstraction leads to the *β-head normal form* of :math:`t`:

.. math::
   t \triangleright … \triangleright λ x_1 :T_1 .~…λ x_k :T_k .~(v~u_1 … u_m )

where :math:`v` is not an abstraction (nor an application). Note that the head
normal form must not be confused with the normal form since some :math:`u_i`
can be reducible. Similar notions of head-normal forms involving δ, ι
and ζ reductions or any combination of those can also be defined.

.. _Admissible-rules-for-global-environments:

Admissible rules for global environments
--------------------------------------------

From the original rules of the type system, one can show the
admissibility of rules which change the local context of definition of
objects in the global environment. We show here the admissible rules
that are used in the discharge mechanism at the end of a section.


.. _Abstraction:

**Abstraction.**
One can modify a global declaration by generalizing it over a
previously assumed constant :math:`c`. For doing that, we need to modify the
reference to the global declaration in the subsequent global
environment and local context by explicitly applying this constant to
the constant :math:`c`.

Below, if :math:`Γ` is a context of the form :math:`[y_1 :A_1 ;~…;~y_n :A_n]`, we write
:math:`∀x:U,~\subst{Γ}{c}{x}` to mean
:math:`[y_1 :∀ x:U,~\subst{A_1}{c}{x};~…;~y_n :∀ x:U,~\subst{A_n}{c}{x}]`
and :math:`\subst{E}{|Γ|}{|Γ|c}` to mean the parallel substitution
:math:`E\{y_1 /(y_1~c)\}…\{y_n/(y_n~c)\}`.


.. _First-abstracting-property:

**First abstracting property:**

.. math::
   \frac{\WF{E;~c:U;~E′;~c′:=t:T;~E″}{Γ}}
        {\WF{E;~c:U;~E′;~c′:=λ x:U.~\subst{t}{c}{x}:∀x:U,~\subst{T}{c}{x};~\subst{E″}{c′}{(c′~c)}}
        {\subst{Γ}{c′}{(c′~c)}}}


.. math::
   \frac{\WF{E;~c:U;~E′;~c′:T;~E″}{Γ}}
        {\WF{E;~c:U;~E′;~c′:∀ x:U,~\subst{T}{c}{x};~\subst{E″}{c′}{(c′~c)}}{\subst{Γ}{c′}{(c′~c)}}}

.. math::
   \frac{\WF{E;~c:U;~E′;~\ind{p}{Γ_I}{Γ_C};~E″}{Γ}}
        {\WFTWOLINES{E;~c:U;~E′;~\ind{p+1}{∀ x:U,~\subst{Γ_I}{c}{x}}{∀ x:U,~\subst{Γ_C}{c}{x}};~
          \subst{E″}{|Γ_I ;Γ_C |}{|Γ_I ;Γ_C | c}}
         {\subst{Γ}{|Γ_I ;Γ_C|}{|Γ_I ;Γ_C | c}}}

One can similarly modify a global declaration by generalizing it over
a previously defined constant :math:`c`. Below, if :math:`Γ` is a context of the form
:math:`[y_1 :A_1 ;~…;~y_n :A_n]`, we write :math:`\subst{Γ}{c}{u}` to mean
:math:`[y_1 :\subst{A_1} {c}{u};~…;~y_n:\subst{A_n} {c}{u}]`.


.. _Second-abstracting-property:

**Second abstracting property:**

.. math::
   \frac{\WF{E;~c:=u:U;~E′;~c′:=t:T;~E″}{Γ}}
        {\WF{E;~c:=u:U;~E′;~c′:=(\letin{x}{u:U}{\subst{t}{c}{x}}):\subst{T}{c}{u};~E″}{Γ}}

.. math::
   \frac{\WF{E;~c:=u:U;~E′;~c′:T;~E″}{Γ}}
        {\WF{E;~c:=u:U;~E′;~c′:\subst{T}{c}{u};~E″}{Γ}}

.. math::
   \frac{\WF{E;~c:=u:U;~E′;~\ind{p}{Γ_I}{Γ_C};~E″}{Γ}}
        {\WF{E;~c:=u:U;~E′;~\ind{p}{\subst{Γ_I}{c}{u}}{\subst{Γ_C}{c}{u}};~E″}{Γ}}

.. _Pruning-the-local-context:

**Pruning the local context.**
If one abstracts or substitutes constants with the above rules then it
may happen that some declared or defined constant does not occur any
more in the subsequent global environment and in the local context.
One can consequently derive the following property.


.. _First-pruning-property:

.. inference:: First pruning property:

   \WF{E;~c:U;~E′}{Γ}
   c~\kw{does not occur in}~E′~\kw{and}~Γ
   --------------------------------------
   \WF{E;E′}{Γ}


.. _Second-pruning-property:

.. inference:: Second pruning property:

   \WF{E;~c:=u:U;~E′}{Γ}
   c~\kw{does not occur in}~E′~\kw{and}~Γ
   --------------------------------------
   \WF{E;E′}{Γ}


.. _The-Calculus-of-Inductive-Construction-with-impredicative-Set:

The Calculus of Inductive Constructions with impredicative Set
-----------------------------------------------------------------

|Coq| can be used as a type checker for the Calculus of Inductive
Constructions with an impredicative sort :math:`\Set` by using the compiler
option ``-impredicative-set``. For example, using the ordinary `coqtop`
command, the following is rejected,

.. example::

   .. coqtop:: all

      Fail Definition id: Set := forall X:Set,X->X.

while it will type check, if one uses instead the `coqtop`
``-impredicative-set`` option..

The major change in the theory concerns the rule for product formation
in the sort :math:`\Set`, which is extended to a domain in any sort:

.. inference:: ProdImp

   E[Γ] ⊢ T : s
   s ∈ \Sort
   E[Γ::(x:T)] ⊢ U : \Set
   ---------------------
   E[Γ] ⊢ ∀ x:T,~U : \Set

This extension has consequences on the inductive definitions which are
allowed. In the impredicative system, one can build so-called *large
inductive definitions* like the example of second-order existential
quantifier (:g:`exSet`).

There should be restrictions on the eliminations which can be
performed on such definitions. The elimination rules in the
impredicative system for sort :math:`\Set` become:



.. inference:: Set1

   s ∈ \{\Prop, \Set\}
   -----------------
   [I:\Set|I→ s]

.. inference:: Set2

   I~\kw{is a small inductive definition}
   s ∈ \{\Type(i)\}
   ----------------
   [I:\Set|I→ s]
