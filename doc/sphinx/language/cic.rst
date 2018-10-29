.. _calculusofinductiveconstructions:


Calculus of Inductive Constructions
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
to a type and takes the form "*for all x of type T, P* ". The expression
“x of type T” is written :g:`x:T`. Informally, :g:`x:T` can be thought as
“x belongs to T”.

The types of types are *sorts*. Types and sorts are themselves terms
so that terms, types and sorts are all components of a common
syntactic language of terms which is described in Section :ref:`terms` but,
first, we describe sorts.


.. _Sorts:

Sorts
~~~~~~~~~~~

All sorts have a type and there is an infinite well-founded typing
hierarchy of sorts whose base sorts are :math:`\Prop` and :math:`\Set`.

The sort :math:`\Prop` intends to be the type of logical propositions. If :math:`M` is a
logical proposition then it denotes the class of terms representing
proofs of :math:`M`. An object :math:`m` belonging to :math:`M` witnesses the fact that :math:`M` is
provable. An object of type :math:`\Prop` is called a proposition.

The sort :math:`\Set` intends to be the type of small sets. This includes data
types such as booleans and naturals, but also products, subsets, and
function types over these data types.

:math:`\Prop` and :math:`\Set` themselves can be manipulated as ordinary terms.
Consequently they also have a type. Because assuming simply that :math:`\Set`
has type :math:`\Set` leads to an inconsistent theory :cite:`Coq86`, the language of
|Cic| has infinitely many sorts. There are, in addition to :math:`\Set` and :math:`\Prop`
a hierarchy of universes :math:`\Type(i)` for any integer :math:`i`.

Like :math:`\Set`, all of the sorts :math:`\Type(i)` contain small sets such as
booleans, natural numbers, as well as products, subsets and function
types over small sets. But, unlike :math:`\Set`, they also contain large sets,
namely the sorts :math:`\Set` and :math:`\Type(j)` for :math:`j<i`, and all products, subsets
and function types over these sorts.

Formally, we call :math:`\Sort` the set of sorts which is defined by:

.. math::
   
   \Sort \equiv \{\Prop,\Set,\Type(i)\;|\; i~∈ ℕ\}

Their properties, such as: :math:`\Prop:\Type(1)`, :math:`\Set:\Type(1)`, and
:math:`\Type(i):\Type(i+1)`, are defined in Section :ref:`subtyping-rules`.

The user does not have to mention explicitly the index :math:`i` when
referring to the universe :math:`\Type(i)`. One only writes :math:`\Type`. The system
itself generates for each instance of :math:`\Type` a new index for the
universe and checks that the constraints between these indexes can be
solved. From the user point of view we consequently have :math:`\Type:\Type`. We
shall make precise in the typing rules the constraints between the
indices.


.. _Implementation-issues:

**Implementation issues** In practice, the Type hierarchy is
implemented using *algebraic
universes*. An algebraic universe :math:`u` is either a variable (a qualified
identifier with a number) or a successor of an algebraic universe (an
expression :math:`u+1`), or an upper bound of algebraic universes (an
expression :math:`\max(u 1 ,...,u n )`), or the base universe (the expression
:math:`0`) which corresponds, in the arity of template polymorphic inductive
types (see Section
:ref:`well-formed-inductive-definitions`),
to the predicative sort :math:`\Set`. A graph of
constraints between the universe variables is maintained globally. To
ensure the existence of a mapping of the universes to the positive
integers, the graph of constraints must remain acyclic. Typing
expressions that violate the acyclicity of the graph of constraints
results in a Universe inconsistency error.

.. seealso:: Section :ref:`printing-universes`.


.. _Terms:

Terms
~~~~~



Terms are built from sorts, variables, constants, abstractions,
applications, local definitions, and products. From a syntactic point
of view, types cannot be distinguished from terms, except that they
cannot start by an abstraction or a constructor. More precisely the
language of the *Calculus of Inductive Constructions* is built from
the following rules.


#. the sorts :math:`\Set`, :math:`\Prop`, :math:`\Type(i)` are terms.
#. variables, hereafter ranged over by letters :math:`x`, :math:`y`, etc., are terms
#. constants, hereafter ranged over by letters :math:`c`, :math:`d`, etc., are terms.
#. if :math:`x` is a variable and :math:`T`, :math:`U` are terms then
   :math:`∀ x:T,U` (:g:`forall x:T, U`   in |Coq| concrete syntax) is a term.
   If :math:`x` occurs in :math:`U`, :math:`∀ x:T,U` reads as
   “for all :math:`x` of type :math:`T`, :math:`U`”.
   As :math:`U` depends on :math:`x`, one says that :math:`∀ x:T,U` is
   a *dependent product*. If :math:`x` does not occur in :math:`U` then
   :math:`∀ x:T,U` reads as
   “if :math:`T` then :math:`U`”. A *non dependent product* can be
   written: :math:`T \rightarrow U`.
#. if :math:`x` is a variable and :math:`T`, :math:`u` are terms then
   :math:`λ x:T . u` (:g:`fun x:T => u`
   in |Coq| concrete syntax) is a term. This is a notation for the
   λ-abstraction of λ-calculus :cite:`Bar81`. The term :math:`λ x:T . u` is a function
   which maps elements of :math:`T` to the expression :math:`u`.
#. if :math:`t` and :math:`u` are terms then :math:`(t~u)` is a term
   (:g:`t u` in |Coq| concrete
   syntax). The term :math:`(t~u)` reads as “t applied to u”.
#. if :g:`x` is a variable, and :math:`t`, :math:`T` and :math:`u` are
   terms then :g:`let x:=t:T in u` is
   a term which denotes the term :math:`u` where the variable :math:`x` is locally bound
   to :math:`t` of type :math:`T`. This stands for the common “let-in” construction of
   functional programs such as ML or Scheme.



.. _Free-variables:

**Free variables.**
The notion of free variables is defined as usual. In the expressions
:g:`λx:T. U` and :g:`∀ x:T, U` the occurrences of :math:`x` in :math:`U` are bound.


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
predicate of type \nat→\nat→ \Prop. The λ-abstraction can serve to build
“ordinary” functions as in :math:`λ x:\nat.(\kw{mult}~x~x)` (i.e.
:g:`fun x:nat => mult x x`
in |Coq| notation) but may build also predicates over the natural
numbers. For instance :math:`λ x:\nat.(\kw{eqnat}~x~0)`
(i.e. :g:`fun x:nat => eqnat x 0`
in |Coq| notation) will represent the predicate of one variable :math:`x` which
asserts the equality of :math:`x` with :math:`0`. This predicate has type
:math:`\nat → \Prop`
and it can be applied to any expression of type :math:`\nat`, say :math:`t`, to give an
object :math:`P~t` of type :math:`\Prop`, namely a proposition.

Furthermore :g:`forall x:nat, P x` will represent the type of functions
which associate to each natural number :math:`n` an object of type :math:`(P~n)` and
consequently represent the type of proofs of the formula “:math:`∀ x. P(x`)”.


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
A typical example is :math:`[x:T;y:=u:U;z:V]`. Notice that the variables
declared in a local context must be distinct. If :math:`Γ` is a local context
that declares some :math:`x`, we
write :math:`x ∈ Γ`. By writing :math:`(x:T) ∈ Γ` we mean that either :math:`x:T` is an
assumption in :math:`Γ` or that there exists some :math:`t` such that :math:`x:=t:T` is a
definition in :math:`Γ`. If :math:`Γ` defines some :math:`x:=t:T`, we also write :math:`(x:=t:T) ∈ Γ`.
For the rest of the chapter, :math:`Γ::(y:T)` denotes the local context :math:`Γ`
enriched with the local assumption :math:`y:T`. Similarly, :math:`Γ::(y:=t:T)` denotes
the local context :math:`Γ` enriched with the local definition :math:`(y:=t:T)`. The
notation :math:`[]` denotes the empty local context. By :math:`Γ_1 ; Γ_2` we mean
concatenation of the local context :math:`Γ_1` and the local context :math:`Γ_2` .


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
such names *constants*. For the rest of the chapter, the :math:`E;c:T` denotes
the global environment :math:`E` enriched with the global assumption :math:`c:T`.
Similarly, :math:`E;c:=t:T` denotes the global environment :math:`E` enriched with the
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
   \WF{E;c:T}{}

.. inference:: W-Global-Def

   \WTE{}{t}{T}
   c \notin E
   ---------------
   \WF{E;c:=t:T}{}

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

.. inference:: Prod-Prop

   \WTEG{T}{s}
   s \in {\Sort}
   \WTE{\Gamma::(x:T)}{U}{\Prop}
   -----------------------------
   \WTEG{\forall~x:T,U}{\Prop}

.. inference:: Prod-Set

   \WTEG{T}{s}
   s \in \{\Prop, \Set\}
   \WTE{\Gamma::(x:T)}{U}{\Set}
   ----------------------------
   \WTEG{\forall~x:T,U}{\Set}

.. inference:: Prod-Type

   \WTEG{T}{\Type(i)}
   \WTE{\Gamma::(x:T)}{U}{\Type(i)}
   --------------------------------
   \WTEG{\forall~x:T,U}{\Type(i)}

.. inference:: Lam

   \WTEG{\forall~x:T,U}{s}
   \WTE{\Gamma::(x:T)}{t}{U}
   ------------------------------------
   \WTEG{\lb x:T\mto t}{\forall x:T, U}

.. inference:: App

   \WTEG{t}{\forall~x:U,T}
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
   :math:`((λ x:T.u) t)` well-typed (where :math:`T` is a type of
   :math:`t`). This is because the value :math:`t` associated to
   :math:`x` may be used in a conversion rule
   (see Section :ref:`Conversion-rules`).


.. _Conversion-rules:

Conversion rules
--------------------

In |Cic|, there is an internal reduction mechanism. In particular, it
can decide if two programs are *intentionally* equal (one says
*convertible*). Convertibility is described in this section.


.. _beta-reduction:

β-reduction
~~~~~~~~~~~

We want to be able to identify some terms as we can identify the
application of a function to a given argument with its result. For
instance the identity function over a given type T can be written
:math:`λx:T. x`. In any global environment :math:`E` and local context
:math:`Γ`, we want to identify any object :math:`a` (of type
:math:`T`) with the application :math:`((λ x:T. x) a)`.  We define for
this a *reduction* (or a *conversion*) rule we call :math:`β`:

.. math::
   
	E[Γ] ⊢ ((λx:T. t) u)~\triangleright_β~\subst{t}{x}{u}

We say that :math:`\subst{t}{x}{u}` is the *β-contraction* of
:math:`((λx:T. t) u)` and, conversely, that :math:`((λ x:T. t) u)` is the
*β-expansion* of :math:`\subst{t}{x}{u}`.

According to β-reduction, terms of the *Calculus of Inductive
Constructions* enjoy some fundamental properties such as confluence,
strong normalization, subject reduction. These results are
theoretically of great importance but we will not detail them here and
refer the interested reader to :cite:`Coq85`.


.. _iota-reduction:

ι-reduction
~~~~~~~~~~~

A specific conversion rule is associated to the inductive objects in
the global environment. We shall give later on (see Section
:ref:`Well-formed-inductive-definitions`) the precise rules but it
just says that a destructor applied to an object built from a
constructor behaves as expected. This reduction is called ι-reduction
and is more precisely studied in :cite:`Moh93,Wer94`.


.. _delta-reduction:

δ-reduction
~~~~~~~~~~~

We may have variables defined in local contexts or constants defined
in the global environment. It is legal to identify such a reference
with its value, that is to expand (or unfold) it into its value. This
reduction is called δ-reduction and shows as follows.

.. inference:: Delta-Local
   
   \WFE{\Gamma}
   (x:=t:T) ∈ Γ
   --------------
   E[Γ] ⊢ x~\triangleright_Δ~t

.. inference:: Delta-Global
   
   \WFE{\Gamma}
   (c:=t:T) ∈ E
   --------------
   E[Γ] ⊢ c~\triangleright_δ~t


.. _zeta-reduction:

ζ-reduction
~~~~~~~~~~~

|Coq| allows also to remove local definitions occurring in terms by
replacing the defined variable by its value. The declaration being
destroyed, this reduction differs from δ-reduction. It is called
ζ-reduction and shows as follows.

.. inference:: Zeta
   
   \WFE{\Gamma}
   \WTEG{u}{U}
   \WTE{\Gamma::(x:=u:U)}{t}{T}
   --------------
   E[Γ] ⊢ \letin{x}{u}{t}~\triangleright_ζ~\subst{t}{x}{u}


.. _eta-expansion:

η-expansion
~~~~~~~~~~~

Another important concept is η-expansion. It is legal to identify any
term :math:`t` of functional type :math:`∀ x:T, U` with its so-called η-expansion

.. math::
   λx:T. (t~x)

for :math:`x` an arbitrary variable name fresh in :math:`t`.


.. note::

   We deliberately do not define η-reduction:

   .. math::
      λ x:T. (t~x) \not\triangleright_η t

   This is because, in general, the type of :math:`t` need not to be convertible
   to the type of :math:`λ x:T. (t~x)`. E.g., if we take :math:`f` such that:

   .. math::
      f : ∀ x:\Type(2),\Type(1)
   
   then

   .. math::
      λ x:\Type(1),(f~x) : ∀ x:\Type(1),\Type(1)
   
   We could not allow

   .. math::
      λ x:Type(1),(f x) \triangleright_η f
   
   because the type of the reduced term :math:`∀ x:\Type(2),\Type(1)` would not be
   convertible to the type of the original term :math:`∀ x:\Type(1),\Type(1).`


.. _convertibility:

Convertibility
~~~~~~~~~~~~~~

Let us write :math:`E[Γ] ⊢ t \triangleright u` for the contextual closure of the
relation :math:`t` reduces to :math:`u` in the global environment
:math:`E` and local context :math:`Γ` with one of the previous
reductions β, δ, ι or ζ.

We say that two terms :math:`t_1` and :math:`t_2` are
*βδιζη-convertible*, or simply *convertible*, or *equivalent*, in the
global environment :math:`E` and local context :math:`Γ` iff there
exist terms :math:`u_1` and :math:`u_2` such that :math:`E[Γ] ⊢ t_1 \triangleright
… \triangleright u_1` and :math:`E[Γ] ⊢ t_2 \triangleright … \triangleright u_2` and either :math:`u_1` and
:math:`u_2` are identical, or they are convertible up to η-expansion,
i.e. :math:`u_1` is :math:`λ x:T. u_1'` and :math:`u_2 x` is
recursively convertible to :math:`u_1'` , or, symmetrically,
:math:`u_2` is :math:`λx:T. u_2'` 
and :math:`u_1 x` is recursively convertible to u_2′ . We then write
:math:`E[Γ] ⊢ t_1 =_{βδιζη} t_2` .

Apart from this we consider two instances of polymorphic and
cumulative (see Chapter :ref:`polymorphicuniverses`) inductive types
(see below) convertible

.. math::
   E[Γ] ⊢ t~w_1 … w_m =_{βδιζη} t~w_1' … w_m'

if we have subtypings (see below) in both directions, i.e.,

.. math::
   E[Γ] ⊢ t~w_1 … w_m ≤_{βδιζη} t~w_1' … w_m'

and

.. math::
   E[Γ] ⊢ t~w_1' … w_m' ≤_{βδιζη} t~w_1 … w_m.

Furthermore, we consider

.. math::
   E[Γ] ⊢ c~v_1 … v_m =_{βδιζη} c'~v_1' … v_m'

convertible if

.. math::
   E[Γ] ⊢ v_i =_{βδιζη} v_i'

and we have that :math:`c` and :math:`c'`
are the same constructors of different instances of the same inductive
types (differing only in universe levels) such that

.. math::
   E[Γ] ⊢ c~v_1 … v_m : t~w_1 … w_m

and

.. math::
   E[Γ] ⊢ c'~v_1' … v_m' : t'~ w_1' … w_m '

and we have

.. math::
   E[Γ] ⊢ t~w_1 … w_m =_{βδιζη} t~w_1' … w_m'.

The convertibility relation allows introducing a new typing rule which
says that two convertible well-formed types have the same inhabitants.


.. _subtyping-rules:

Subtyping rules
-------------------

At the moment, we did not take into account one rule between universes
which says that any term in a universe of index i is also a term in
the universe of index i+1 (this is the *cumulativity* rule of |Cic|).
This property extends the equivalence relation of convertibility into
a *subtyping* relation inductively defined by:


#. if :math:`E[Γ] ⊢ t =_{βδιζη} u` then :math:`E[Γ] ⊢ t ≤_{βδιζη} u`,
#. if :math:`i ≤ j` then :math:`E[Γ] ⊢ \Type(i) ≤_{βδιζη} \Type(j)`,
#. for any :math:`i`, :math:`E[Γ] ⊢ \Set ≤_{βδιζη} \Type(i)`,
#. :math:`E[Γ] ⊢ \Prop ≤_{βδιζη} \Set`, hence, by transitivity,
   :math:`E[Γ] ⊢ \Prop ≤_{βδιζη} \Type(i)`, for any :math:`i`
#. if :math:`E[Γ] ⊢ T =_{βδιζη} U` and
   :math:`E[Γ::(x:T)] ⊢ T' ≤_{βδιζη} U'` then
   :math:`E[Γ] ⊢ ∀x:T, T′ ≤_{βδιζη} ∀ x:U, U′`.
#. if :math:`\ind{p}{Γ_I}{Γ_C}` is a universe polymorphic and cumulative
   (see Chapter :ref:`polymorphicuniverses`) inductive type (see below)
   and
   :math:`(t : ∀Γ_P ,∀Γ_{\mathit{Arr}(t)}, \Sort)∈Γ_I`
   and
   :math:`(t' : ∀Γ_P' ,∀Γ_{\mathit{Arr}(t)}', \Sort')∈Γ_I`
   are two different instances of *the same* inductive type (differing only in
   universe levels) with constructors

   .. math::
      [c_1 : ∀Γ_P ,∀ T_{1,1} … T_{1,n_1} , t~v_{1,1} … v_{1,m} ;…;
      c_k : ∀Γ_P ,∀ T_{k,1} … T_{k,n_k} ,t~v_{n,1} … v_{n,m} ]

   and

   .. math::
      [c_1 : ∀Γ_P' ,∀ T_{1,1}' … T_{1,n_1}' , t'~v_{1,1}' … v_{1,m}' ;…;
      c_k : ∀Γ_P' ,∀ T_{k,1}' … T_{k,n_k}' ,t'~v_{n,1}' … v_{n,m}' ]
   
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

   where :math:`Γ_{\mathit{Arr}(t)} = [a_1 : A_1 ;  … ; a_l : A_l ]` and
   :math:`Γ_{\mathit{Arr}(t)}' = [a_1 : A_1';  … ; a_l : A_l']`.


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
:math:`λ x_1 :T_1 . … λ x_k :T_k . (t_0~t_1 … t_n )` where :math:`t_0` is not an
application. We say then that :math:`t_0` is the *head of* :math:`t`. If we assume
that :math:`t_0` is :math:`λ x:T. u_0` then one step of β-head reduction of :math:`t` is:

.. math::
   λ x_1 :T_1 . … λ x_k :T_k . (λ x:T. u_0~t_1 … t_n ) \triangleright
   λ (x_1 :T_1 )…(x_k :T_k ). (\subst{u_0}{x}{t_1}~t_2 … t_n )
   
Iterating the process of head reduction until the head of the reduced
term is no more an abstraction leads to the *β-head normal form* of :math:`t`:

.. math::
   t \triangleright … \triangleright λ x_1 :T_1 . …λ x_k :T_k . (v~u_1 … u_m )
   
where :math:`v` is not an abstraction (nor an application). Note that the head
normal form must not be confused with the normal form since some :math:`u_i`
can be reducible. Similar notions of head-normal forms involving δ, ι
and ζ reductions or any combination of those can also be defined.


.. _inductive-definitions:

Inductive Definitions
-------------------------

Formally, we can represent any *inductive definition* as
:math:`\ind{p}{Γ_I}{Γ_C}` where:

+ :math:`Γ_I` determines the names and types of inductive types;
+ :math:`Γ_C` determines the names and types of constructors of these
  inductive types;
+ :math:`p` determines the number of parameters of these inductive types.


These inductive definitions, together with global assumptions and
global definitions, then form the global environment. Additionally,
for any :math:`p` there always exists :math:`Γ_P =[a_1 :A_1 ;…;a_p :A_p ]` such that
each :math:`T` in :math:`(t:T)∈Γ_I \cup Γ_C` can be written as: :math:`∀Γ_P , T'` where :math:`Γ_P` is
called the *context of parameters*. Furthermore, we must have that
each :math:`T` in :math:`(t:T)∈Γ_I` can be written as: :math:`∀Γ_P,∀Γ_{\mathit{Arr}(t)}, S` where
:math:`Γ_{\mathit{Arr}(t)}` is called the *Arity* of the inductive type t and :math:`S` is called
the sort of the inductive type t (not to be confused with :math:`\Sort` which is the set of sorts).

.. example::

   The declaration for parameterized lists is:

   .. math::
      \ind{1}{[\List:\Set→\Set]}{\left[\begin{array}{rcl}
      \Nil & : & \forall A:\Set,\List~A \\
      \cons & : & \forall A:\Set, A→ \List~A→ \List~A
      \end{array}
      \right]}

   which corresponds to the result of the |Coq| declaration:

   .. coqtop:: in

      Inductive list (A:Set) : Set :=
      | nil : list A
      | cons : A -> list A -> list A.

.. example::

   The declaration for a mutual inductive definition of tree and forest
   is:

   .. math::
      \ind{0}{\left[\begin{array}{rcl}\tree&:&\Set\\\forest&:&\Set\end{array}\right]}
       {\left[\begin{array}{rcl}
                \node &:& \forest → \tree\\
                \emptyf &:& \forest\\
                \consf &:& \tree → \forest → \forest\\
                          \end{array}\right]}

   which corresponds to the result of the |Coq| declaration:

   .. coqtop:: in

      Inductive tree : Set :=
      | node : forest -> tree
      with forest : Set :=
      | emptyf : forest
      | consf : tree -> forest -> forest.

.. example::

   The declaration for a mutual inductive definition of even and odd is:

   .. math::
      \ind{0}{\left[\begin{array}{rcl}\even&:&\nat → \Prop \\
                                      \odd&:&\nat → \Prop \end{array}\right]}
       {\left[\begin{array}{rcl}
                \evenO &:& \even~0\\
                \evenS &:& \forall n, \odd~n → \even~(\kw{S}~n)\\
                \oddS &:& \forall n, \even~n → \odd~(\kw{S}~n)
                          \end{array}\right]}

   which corresponds to the result of the |Coq| declaration:

   .. coqtop:: in

      Inductive even : nat -> Prop :=
      | even_O : even 0
      | even_S : forall n, odd n -> even (S n)
      with odd : nat -> prop :=
      | odd_S : forall n, even n -> odd (S n).



.. _Types-of-inductive-objects:

Types of inductive objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We have to give the type of constants in a global environment E which
contains an inductive declaration.

.. inference:: Ind
	       
   \WFE{Γ}
   \ind{p}{Γ_I}{Γ_C} ∈ E
   (a:A)∈Γ_I
   ---------------------
   E[Γ] ⊢ a : A

.. inference:: Constr
	       
   \WFE{Γ}
   \ind{p}{Γ_I}{Γ_C} ∈ E
   (c:C)∈Γ_C
   ---------------------
   E[Γ] ⊢ c : C

.. example::

   Provided that our environment :math:`E` contains inductive definitions we showed before,
   these two inference rules above enable us to conclude that:

   .. math::
      \begin{array}{l}
      E[Γ] ⊢ \even : \nat→\Prop\\
      E[Γ] ⊢ \odd : \nat→\Prop\\
      E[Γ] ⊢ \even\_O : \even~O\\
      E[Γ] ⊢ \even\_S : \forall~n:\nat, \odd~n → \even~(S~n)\\
      E[Γ] ⊢ \odd\_S : \forall~n:\nat, \even~n → \odd~(S~n)
      \end{array}




.. _Well-formed-inductive-definitions:

Well-formed inductive definitions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot accept any inductive declaration because some of them lead
to inconsistent systems. We restrict ourselves to definitions which
satisfy a syntactic criterion of positivity. Before giving the formal
rules, we need a few definitions:

Arity of a given sort
+++++++++++++++++++++

A type :math:`T` is an *arity of sort* :math:`s` if it converts to the sort :math:`s` or to a
product :math:`∀ x:T,U` with :math:`U` an arity of sort :math:`s`.

.. example::

   :math:`A→\Set` is an arity of sort :math:`\Set`. :math:`∀ A:\Prop,A→ \Prop` is an arity of sort
   :math:`\Prop`.


Arity
+++++
A type :math:`T` is an *arity* if there is a :math:`s∈ \Sort` such that :math:`T` is an arity of
sort :math:`s`.


.. example::

   :math:`A→ Set` and :math:`∀ A:\Prop,A→ \Prop` are arities.


Type constructor
++++++++++++++++
We say that T is a *type of constructor of I* in one of the following
two cases:

+ :math:`T` is :math:`(I~t_1 … t_n )`
+ :math:`T` is :math:`∀ x:U,T'` where :math:`T'` is also a type of constructor of :math:`I`

.. example::

   :math:`\nat` and :math:`\nat→\nat` are types of constructor of :math:`\nat`.
   :math:`∀ A:Type,\List~A` and :math:`∀ A:Type,A→\List~A→\List~A` are types of constructor of :math:`\List`.

.. _positivity:

Positivity Condition
++++++++++++++++++++

The type of constructor :math:`T` will be said to *satisfy the positivity
condition* for a constant :math:`X` in the following cases:

+ :math:`T=(X~t_1 … t_n )` and :math:`X` does not occur free in any :math:`t_i`
+ :math:`T=∀ x:U,V` and :math:`X` occurs only strictly positively in :math:`U` and the type :math:`V`
  satisfies the positivity condition for :math:`X`.
  
Strict positivity
+++++++++++++++++

The constant :math:`X` *occurs strictly positively* in :math:`T` in the following
cases:


+ :math:`X` does not occur in :math:`T`
+ :math:`T` converts to :math:`(X~t_1 … t_n )` and :math:`X` does not occur in any of :math:`t_i`
+ :math:`T` converts to :math:`∀ x:U,V` and :math:`X` does not occur in type :math:`U` but occurs
  strictly positively in type :math:`V`
+ :math:`T` converts to :math:`(I~a_1 … a_m~t_1 … t_p )` where :math:`I` is the name of an
  inductive declaration of the form
  
  .. math::
     \ind{m}{I:A}{c_1 :∀ p_1 :P_1 ,… ∀p_m :P_m ,C_1 ;…;c_n :∀ p_1 :P_1 ,… ∀p_m :P_m ,C_n}
     
  (in particular, it is
  not mutually defined and it has :math:`m` parameters) and :math:`X` does not occur in
  any of the :math:`t_i`, and the (instantiated) types of constructor
  :math:`\subst{C_i}{p_j}{a_j}_{j=1… m}` of :math:`I` satisfy the nested positivity condition for :math:`X`

Nested Positivity
+++++++++++++++++

The type of constructor :math:`T` of :math:`I` *satisfies the nested positivity
condition* for a constant :math:`X` in the following cases:

+ :math:`T=(I~b_1 … b_m~u_1 … u_p)`, :math:`I` is an inductive definition with :math:`m`
  parameters and :math:`X` does not occur in any :math:`u_i`
+ :math:`T=∀ x:U,V` and :math:`X` occurs only strictly positively in :math:`U` and the type :math:`V`
  satisfies the nested positivity condition for :math:`X`


.. example::

   For instance, if one considers the following variant of a tree type
   branching over the natural numbers:

   .. coqtop:: in

      Inductive nattree (A:Type) : Type :=
      | leaf : nattree A
      | node : A -> (nat -> nattree A) -> nattree A.
      End TreeExample.

   Then every instantiated constructor of ``nattree A`` satisfies the nested positivity
   condition for ``nattree``:

   + Type ``nattree A`` of constructor ``leaf`` satisfies the positivity condition for
     ``nattree`` because ``nattree`` does not appear in any (real) arguments of the
     type of that constructor (primarily because ``nattree`` does not have any (real)
     arguments) ... (bullet 1)

   + Type ``A → (nat → nattree A) → nattree A`` of constructor ``node`` satisfies the
     positivity condition for ``nattree`` because:

     - ``nattree`` occurs only strictly positively in ``A`` ... (bullet 3)

     - ``nattree`` occurs only strictly positively in ``nat → nattree A`` ... (bullet 3 + 2)

     - ``nattree`` satisfies the positivity condition for ``nattree A`` ... (bullet 1)

.. _Correctness-rules:

Correctness rules
+++++++++++++++++

We shall now describe the rules allowing the introduction of a new
inductive definition.

Let :math:`E` be a global environment and :math:`Γ_P`, :math:`Γ_I`, :math:`Γ_C` be contexts
such that :math:`Γ_I` is :math:`[I_1 :∀ Γ_P ,A_1 ;…;I_k :∀ Γ_P ,A_k]`, and
:math:`Γ_C` is :math:`[c_1:∀ Γ_P ,C_1 ;…;c_n :∀ Γ_P ,C_n ]`. Then

.. inference:: W-Ind

   \WFE{Γ_P}
   (E[Γ_P ] ⊢ A_j : s_j )_{j=1… k}
   (E[Γ_I ;Γ_P ] ⊢ C_i : s_{q_i} )_{i=1… n}
   ------------------------------------------
   \WF{E;\ind{p}{Γ_I}{Γ_C}}{Γ}
   

provided that the following side conditions hold:

    + :math:`k>0` and all of :math:`I_j` and :math:`c_i` are distinct names for :math:`j=1… k` and :math:`i=1… n`,
    + :math:`p` is the number of parameters of :math:`\ind{p}{Γ_I}{Γ_C}` and :math:`Γ_P` is the
      context of parameters,
    + for :math:`j=1… k` we have that :math:`A_j` is an arity of sort :math:`s_j` and :math:`I_j ∉ E`,
    + for :math:`i=1… n` we have that :math:`C_i` is a type of constructor of :math:`I_{q_i}` which
      satisfies the positivity condition for :math:`I_1 … I_k` and :math:`c_i ∉ Γ ∪ E`.

One can remark that there is a constraint between the sort of the
arity of the inductive type and the sort of the type of its
constructors which will always be satisfied for the impredicative
sort :math:`\Prop` but may fail to define inductive definition on sort :math:`\Set` and
generate constraints between universes for inductive definitions in
the Type hierarchy.


.. example::

   It is well known that the existential quantifier can be encoded as an
   inductive definition. The following declaration introduces the second-
   order existential quantifier :math:`∃ X.P(X)`.

   .. coqtop:: in

      Inductive exProp (P:Prop->Prop) : Prop :=
      | exP_intro : forall X:Prop, P X -> exProp P.

   The same definition on :math:`\Set` is not allowed and fails:

   .. coqtop:: all

      Fail Inductive exSet (P:Set->Prop) : Set :=
      exS_intro : forall X:Set, P X -> exSet P.

   It is possible to declare the same inductive definition in the
   universe :math:`\Type`. The :g:`exType` inductive definition has type
   :math:`(\Type(i)→\Prop)→\Type(j)` with the constraint that the parameter :math:`X` of :math:`\kw{exT}_{\kw{intro}}`
   has type :math:`\Type(k)` with :math:`k<j` and :math:`k≤ i`.

   .. coqtop:: all

      Inductive exType (P:Type->Prop) : Type :=
      exT_intro : forall X:Type, P X -> exType P.



.. _Template-polymorphism:

Template polymorphism
+++++++++++++++++++++

Inductive types declared in :math:`\Type` are polymorphic over their arguments
in :math:`\Type`. If :math:`A` is an arity of some sort and :math:`s` is a sort, we write :math:`A_{/s}`
for the arity obtained from :math:`A` by replacing its sort with :math:`s`.
Especially, if :math:`A` is well-typed in some global environment and local
context, then :math:`A_{/s}` is typable by typability of all products in the
Calculus of Inductive Constructions. The following typing rule is
added to the theory.

Let :math:`\ind{p}{Γ_I}{Γ_C}` be an inductive definition. Let
:math:`Γ_P = [p_1 :P_1 ;…;p_p :P_p ]` be its context of parameters,
:math:`Γ_I = [I_1:∀ Γ_P ,A_1 ;…;I_k :∀ Γ_P ,A_k ]` its context of definitions and
:math:`Γ_C = [c_1 :∀ Γ_P ,C_1 ;…;c_n :∀ Γ_P ,C_n]` its context of constructors,
with :math:`c_i` a constructor of :math:`I_{q_i}`. Let :math:`m ≤ p` be the length of the
longest prefix of parameters such that the :math:`m` first arguments of all
occurrences of all :math:`I_j` in all :math:`C_k` (even the occurrences in the
hypotheses of :math:`C_k`) are exactly applied to :math:`p_1 … p_m` (:math:`m` is the number
of *recursively uniform parameters* and the :math:`p−m` remaining parameters
are the *recursively non-uniform parameters*). Let :math:`q_1 , …, q_r` , with
:math:`0≤ r≤ m`, be a (possibly) partial instantiation of the recursively
uniform parameters of :math:`Γ_P` . We have:

.. inference:: Ind-Family

   \left\{\begin{array}{l}
   \ind{p}{Γ_I}{Γ_C} \in E\\
   (E[]  ⊢ q_l : P'_l)_{l=1\ldots r}\\
   (E[]  ⊢ P'_l ≤_{βδιζη} \subst{P_l}{p_u}{q_u}_{u=1\ldots l-1})_{l=1\ldots r}\\
   1 \leq j \leq k
   \end{array}
   \right.
   -----------------------------
   E[] ⊢ I_j~q_1 … q_r :∀ [p_{r+1} :P_{r+1} ;…;p_p :P_p], (A_j)_{/s_j}

provided that the following side conditions hold:

    + :math:`Γ_{P′}` is the context obtained from :math:`Γ_P` by replacing each :math:`P_l` that is
      an arity with :math:`P_l'` for :math:`1≤ l ≤ r` (notice that :math:`P_l` arity implies :math:`P_l'`
      arity since :math:`(E[] ⊢ P_l' ≤_{βδιζη} \subst{P_l}{p_u}{q_u}_{u=1\ldots l-1} )`;
    + there are sorts :math:`s_i` , for :math:`1 ≤ i ≤ k` such that, for
      :math:`Γ_{I'} = [I_1 :∀ Γ_{P'} ,(A_1)_{/s_1} ;…;I_k :∀ Γ_{P'} ,(A_k)_{/s_k}]`
      we have :math:`(E[Γ_{I′} ;Γ_{P′}] ⊢ C_i : s_{q_i})_{i=1… n}` ;
    + the sorts :math:`s_i` are such that all eliminations, to
      :math:`\Prop`, :math:`\Set` and :math:`\Type(j)`, are allowed
      (see Section :ref:`Destructors`).



Notice that if :math:`I_j~q_1 … q_r` is typable using the rules **Ind-Const** and
**App**, then it is typable using the rule **Ind-Family**. Conversely, the
extended theory is not stronger than the theory without **Ind-Family**. We
get an equiconsistency result by mapping each :math:`\ind{p}{Γ_I}{Γ_C}`
occurring into a given derivation into as many different inductive
types and constructors as the number of different (partial)
replacements of sorts, needed for this derivation, in the parameters
that are arities (this is possible because :math:`\ind{p}{Γ_I}{Γ_C}` well-formed
implies that :math:`\ind{p}{Γ_{I'}}{Γ_{C'}}` is well-formed and has the
same allowed eliminations, where :math:`Γ_{I′}` is defined as above and
:math:`Γ_{C′} = [c_1 :∀ Γ_{P′} ,C_1 ;…;c_n :∀ Γ_{P′} ,C_n ]`). That is, the changes in the
types of each partial instance :math:`q_1 … q_r` can be characterized by the
ordered sets of arity sorts among the types of parameters, and to each
signature is associated a new inductive definition with fresh names.
Conversion is preserved as any (partial) instance :math:`I_j~q_1 … q_r` or
:math:`C_i~q_1 … q_r` is mapped to the names chosen in the specific instance of
:math:`\ind{p}{Γ_I}{Γ_C}`.

In practice, the rule **Ind-Family** is used by |Coq| only when all the
inductive types of the inductive definition are declared with an arity
whose sort is in the Type hierarchy. Then, the polymorphism is over
the parameters whose type is an arity of sort in the Type hierarchy.
The sorts :math:`s_j` are chosen canonically so that each :math:`s_j` is minimal with
respect to the hierarchy :math:`\Prop ⊂ \Set_p ⊂ \Type` where :math:`\Set_p` is predicative
:math:`\Set`. More precisely, an empty or small singleton inductive definition
(i.e. an inductive definition of which all inductive types are
singleton – see Section :ref:`Destructors`) is set in :math:`\Prop`, a small non-singleton
inductive type is set in :math:`\Set` (even in case :math:`\Set` is impredicative – see
Section The-Calculus-of-Inductive-Construction-with-impredicative-Set_),
and otherwise in the Type hierarchy.

Note that the side-condition about allowed elimination sorts in the
rule **Ind-Family** is just to avoid to recompute the allowed elimination
sorts at each instance of a pattern matching (see Section :ref:`Destructors`). As
an example, let us consider the following definition:

.. example::

   .. coqtop:: in

      Inductive option (A:Type) : Type :=
      | None : option A
      | Some : A -> option A.

As the definition is set in the Type hierarchy, it is used
polymorphically over its parameters whose types are arities of a sort
in the Type hierarchy. Here, the parameter :math:`A` has this property, hence,
if :g:`option` is applied to a type in :math:`\Set`, the result is in :math:`\Set`. Note that
if :g:`option` is applied to a type in :math:`\Prop`, then, the result is not set in
:math:`\Prop` but in :math:`\Set` still. This is because :g:`option` is not a singleton type
(see Section :ref:`Destructors`) and it would lose the elimination to :math:`\Set` and :math:`\Type`
if set in :math:`\Prop`.

.. example::

   .. coqtop:: all

      Check (fun A:Set => option A).
      Check (fun A:Prop => option A).

Here is another example.

.. example::

   .. coqtop:: in

      Inductive prod (A B:Type) : Type := pair : A -> B -> prod A B.

As :g:`prod` is a singleton type, it will be in :math:`\Prop` if applied twice to
propositions, in :math:`\Set` if applied twice to at least one type in :math:`\Set` and
none in :math:`\Type`, and in :math:`\Type` otherwise. In all cases, the three kind of
eliminations schemes are allowed.

.. example::

   .. coqtop:: all

      Check (fun A:Set => prod A).
      Check (fun A:Prop => prod A A).
      Check (fun (A:Prop) (B:Set) => prod A B).
      Check (fun (A:Type) (B:Prop) => prod A B).

.. note::
   Template polymorphism used to be called “sort-polymorphism of
   inductive types” before universe polymorphism
   (see Chapter :ref:`polymorphicuniverses`) was introduced.


.. _Destructors:

Destructors
~~~~~~~~~~~~~~~~~

The specification of inductive definitions with arities and
constructors is quite natural. But we still have to say how to use an
object in an inductive type.

This problem is rather delicate. There are actually several different
ways to do that. Some of them are logically equivalent but not always
equivalent from the computational point of view or from the user point
of view.

From the computational point of view, we want to be able to define a
function whose domain is an inductively defined type by using a
combination of case analysis over the possible constructors of the
object and recursion.

Because we need to keep a consistent theory and also we prefer to keep
a strongly normalizing reduction, we cannot accept any sort of
recursion (even terminating). So the basic idea is to restrict
ourselves to primitive recursive functions and functionals.

For instance, assuming a parameter :g:`A:Set` exists in the local context,
we want to build a function length of type :g:`list A -> nat` which computes
the length of the list, such that :g:`(length (nil A)) = O` and :g:`(length
(cons A a l)) = (S (length l))`. We want these equalities to be
recognized implicitly and taken into account in the conversion rule.

From the logical point of view, we have built a type family by giving
a set of constructors. We want to capture the fact that we do not have
any other way to build an object in this type. So when trying to prove
a property about an object :math:`m` in an inductive definition it is enough
to enumerate all the cases where :math:`m` starts with a different
constructor.

In case the inductive definition is effectively a recursive one, we
want to capture the extra property that we have built the smallest
fixed point of this recursive equation. This says that we are only
manipulating finite objects. This analysis provides induction
principles. For instance, in order to prove :g:`∀ l:list A,(has_length A l
(length l))` it is enough to prove:


+ :g:`(has_length A (nil A) (length (nil A)))`
+ :g:`∀ a:A, ∀ l:list A, (has_length A l (length l)) →`
  :g:`(has_length A (cons A a l) (length (cons A a l)))`


which given the conversion equalities satisfied by length is the same
as proving:


+ :g:`(has_length A (nil A) O)`
+ :g:`∀ a:A, ∀ l:list A, (has_length A l (length l)) →`
  :g:`(has_length A (cons A a l) (S (length l)))`


One conceptually simple way to do that, following the basic scheme
proposed by Martin-Löf in his Intuitionistic Type Theory, is to
introduce for each inductive definition an elimination operator. At
the logical level it is a proof of the usual induction principle and
at the computational level it implements a generic operator for doing
primitive recursion over the structure.

But this operator is rather tedious to implement and use. We choose in
this version of |Coq| to factorize the operator for primitive recursion
into two more primitive operations as was first suggested by Th.
Coquand in :cite:`Coq92`. One is the definition by pattern matching. The
second one is a definition by guarded fixpoints.


.. _match-construction:

The match ... with ... end construction
+++++++++++++++++++++++++++++++++++++++

The basic idea of this operator is that we have an object :math:`m` in an
inductive type :math:`I` and we want to prove a property which possibly
depends on :math:`m`. For this, it is enough to prove the property for
:math:`m = (c_i~u_1 … u_{p_i} )` for each constructor of :math:`I`.
The |Coq| term for this proof
will be written:

.. math::
   \Match~m~\with~(c_1~x_{11} ... x_{1p_1} ) ⇒ f_1 | … | (c_n~x_{n1} ... x_{np_n} ) ⇒ f_n \kwend

In this expression, if :math:`m` eventually happens to evaluate to
:math:`(c_i~u_1 … u_{p_i})` then the expression will behave as specified in its :math:`i`-th branch
and it will reduce to :math:`f_i` where the :math:`x_{i1} …x_{ip_i}` are replaced by the
:math:`u_1 … u_{p_i}` according to the ι-reduction.

Actually, for type checking a :math:`\Match…\with…\kwend` expression we also need
to know the predicate P to be proved by case analysis. In the general
case where :math:`I` is an inductively defined :math:`n`-ary relation, :math:`P` is a predicate
over :math:`n+1` arguments: the :math:`n` first ones correspond to the arguments of :math:`I`
(parameters excluded), and the last one corresponds to object :math:`m`. |Coq|
can sometimes infer this predicate but sometimes not. The concrete
syntax for describing this predicate uses the :math:`\as…\In…\return`
construction. For instance, let us assume that :math:`I` is an unary predicate
with one parameter and one argument. The predicate is made explicit
using the syntax:

.. math::
   \Match~m~\as~x~\In~I~\_~a~\return~P~\with~
   (c_1~x_{11} ... x_{1p_1} ) ⇒ f_1 | …
   | (c_n~x_{n1} ... x_{np_n} ) ⇒ f_n~\kwend
   
The :math:`\as` part can be omitted if either the result type does not depend
on :math:`m` (non-dependent elimination) or :math:`m` is a variable (in this case, :math:`m`
can occur in :math:`P` where it is considered a bound variable). The :math:`\In` part
can be omitted if the result type does not depend on the arguments
of :math:`I`. Note that the arguments of :math:`I` corresponding to parameters *must*
be :math:`\_`, because the result type is not generalized to all possible
values of the parameters. The other arguments of :math:`I` (sometimes called
indices in the literature) have to be variables (:math:`a` above) and these
variables can occur in :math:`P`. The expression after :math:`\In` must be seen as an
*inductive type pattern*. Notice that expansion of implicit arguments
and notations apply to this pattern. For the purpose of presenting the
inference rules, we use a more compact notation:

.. math::
   \case(m,(λ a x . P), λ x_{11} ... x_{1p_1} . f_1~| … |~λ x_{n1} ...x_{np_n} . f_n )


.. _Allowed-elimination-sorts:

**Allowed elimination sorts.** An important question for building the typing rule for match is what
can be the type of :math:`λ a x . P` with respect to the type of :math:`m`. If :math:`m:I`
and :math:`I:A` and :math:`λ a x . P : B` then by :math:`[I:A|B]` we mean that one can use
:math:`λ a x . P` with :math:`m` in the above match-construct.


.. _cic_notations:

**Notations.** The :math:`[I:A|B]` is defined as the smallest relation satisfying the
following rules: We write :math:`[I|B]` for :math:`[I:A|B]` where :math:`A` is the type of :math:`I`.

The case of inductive definitions in sorts :math:`\Set` or :math:`\Type` is simple.
There is no restriction on the sort of the predicate to be eliminated.

.. inference:: Prod

   [(I~x):A′|B′]
   -----------------------
   [I:∀ x:A, A′|∀ x:A, B′]

   
.. inference:: Set & Type

   s_1 ∈ \{\Set,\Type(j)\}
   s_2 ∈ \Sort
   ----------------
   [I:s_1 |I→ s_2 ]


The case of Inductive definitions of sort :math:`\Prop` is a bit more
complicated, because of our interpretation of this sort. The only
harmless allowed elimination, is the one when predicate :math:`P` is also of
sort :math:`\Prop`.

.. inference:: Prop
	       
   ~
   ---------------
   [I:Prop|I→Prop]


:math:`\Prop` is the type of logical propositions, the proofs of properties :math:`P` in
:math:`\Prop` could not be used for computation and are consequently ignored by
the extraction mechanism. Assume :math:`A` and :math:`B` are two propositions, and the
logical disjunction :math:`A ∨ B` is defined inductively by:

.. example::

   .. coqtop:: in

      Inductive or (A B:Prop) : Prop :=
      or_introl : A -> or A B | or_intror : B -> or A B.


The following definition which computes a boolean value by case over
the proof of :g:`or A B` is not accepted:

.. example::

   .. coqtop:: all

      Fail Definition choice (A B: Prop) (x:or A B) :=
      match x with or_introl _ _ a => true | or_intror _ _ b => false end.
   
From the computational point of view, the structure of the proof of
:g:`(or A B)` in this term is needed for computing the boolean value.

In general, if :math:`I` has type :math:`\Prop` then :math:`P` cannot have type :math:`I→Set,` because
it will mean to build an informative proof of type :math:`(P~m)` doing a case
analysis over a non-computational object that will disappear in the
extracted program. But the other way is safe with respect to our
interpretation we can have :math:`I` a computational object and :math:`P` a
non-computational one, it just corresponds to proving a logical property
of a computational object.

In the same spirit, elimination on :math:`P` of type :math:`I→Type` cannot be allowed
because it trivially implies the elimination on :math:`P` of type :math:`I→ Set` by
cumulativity. It also implies that there are two proofs of the same
property which are provably different, contradicting the proof-
irrelevance property which is sometimes a useful axiom:

.. example::

   .. coqtop:: all

      Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

The elimination of an inductive definition of type :math:`\Prop` on a predicate
:math:`P` of type :math:`I→ Type` leads to a paradox when applied to impredicative
inductive definition like the second-order existential quantifier
:g:`exProp` defined above, because it gives access to the two projections on
this type.


.. _Empty-and-singleton-elimination:

**Empty and singleton elimination.** There are special inductive definitions in
:math:`\Prop` for which more eliminations are allowed.

.. inference:: Prop-extended
	       
   I~\kw{is an empty or singleton definition}
   s ∈ \Sort
   -------------------------------------
   [I:Prop|I→ s]

A *singleton definition* has only one constructor and all the
arguments of this constructor have type :math:`\Prop`. In that case, there is a
canonical way to interpret the informative extraction on an object in
that type, such that the elimination on any sort :math:`s` is legal. Typical
examples are the conjunction of non-informative propositions and the
equality. If there is a hypothesis :math:`h:a=b` in the local context, it can
be used for rewriting not only in logical propositions but also in any
type.

.. example::

   .. coqtop:: all

      Print eq_rec.
      Require Extraction.
      Extraction eq_rec.

An empty definition has no constructors, in that case also,
elimination on any sort is allowed.


.. _Type-of-branches:

**Type of branches.**
Let :math:`c` be a term of type :math:`C`, we assume :math:`C` is a type of constructor for an
inductive type :math:`I`. Let :math:`P` be a term that represents the property to be
proved. We assume :math:`r` is the number of parameters and :math:`p` is the number of
arguments.

We define a new type :math:`\{c:C\}^P` which represents the type of the branch
corresponding to the :math:`c:C` constructor.

.. math::
   \begin{array}{ll}
   \{c:(I~p_1\ldots p_r\ t_1 \ldots t_p)\}^P &\equiv (P~t_1\ldots ~t_p~c) \\
   \{c:\forall~x:T,C\}^P &\equiv \forall~x:T,\{(c~x):C\}^P 
   \end{array}

We write :math:`\{c\}^P` for :math:`\{c:C\}^P` with :math:`C` the type of :math:`c`.


.. example::

   The following term in concrete syntax::

       match t as l return P' with
       | nil _ => t1
       | cons _ hd tl => t2
       end


   can be represented in abstract syntax as

   .. math::
      \case(t,P,f 1 | f 2 )

   where

   .. math::
      :nowrap:

      \begin{eqnarray*}
        P & = & \lambda~l~.~P^\prime\\
        f_1 & = & t_1\\
        f_2 & = & \lambda~(hd:\nat)~.~\lambda~(tl:\List~\nat)~.~t_2
      \end{eqnarray*}

   According to the definition:

   .. math::
      \{(\kw{nil}~\nat)\}^P ≡ \{(\kw{nil}~\nat) : (\List~\nat)\}^P ≡ (P~(\kw{nil}~\nat))

   .. math::

      \begin{array}{rl}
      \{(\kw{cons}~\nat)\}^P & ≡\{(\kw{cons}~\nat) : (\nat→\List~\nat→\List~\nat)\}^P \\
      & ≡∀ n:\nat, \{(\kw{cons}~\nat~n) : \List~\nat→\List~\nat)\}^P \\
      & ≡∀ n:\nat, ∀ l:\List~\nat, \{(\kw{cons}~\nat~n~l) : \List~\nat)\}^P \\
      & ≡∀ n:\nat, ∀ l:\List~\nat,(P~(\kw{cons}~\nat~n~l)).
      \end{array}

   Given some :math:`P` then :math:`\{(\kw{nil}~\nat)\}^P` represents the expected type of :math:`f_1` ,
   and :math:`\{(\kw{cons}~\nat)\}^P` represents the expected type of :math:`f_2`.


.. _Typing-rule:

**Typing rule.**
Our very general destructor for inductive definition enjoys the
following typing rule

.. inference:: match

   \begin{array}{l}
   E[Γ] ⊢ c : (I~q_1 … q_r~t_1 … t_s ) \\
   E[Γ] ⊢ P : B \\
   [(I~q_1 … q_r)|B] \\
   (E[Γ] ⊢ f_i : \{(c_{p_i}~q_1 … q_r)\}^P)_{i=1… l}
   \end{array}
   ------------------------------------------------
   E[Γ] ⊢ \case(c,P,f_1  |… |f_l ) : (P~t_1 … t_s~c)

provided :math:`I` is an inductive type in a
definition :math:`\ind{r}{Γ_I}{Γ_C}` with :math:`Γ_C = [c_1 :C_1 ;…;c_n :C_n ]` and
:math:`c_{p_1} … c_{p_l}` are the only constructors of :math:`I`.



.. example::

   Below is a typing rule for the term shown in the previous example:

   .. inference:: list example

     \begin{array}{l}
       E[Γ] ⊢ t : (\List ~\nat) \\
       E[Γ] ⊢ P : B \\
       [(\List ~\nat)|B] \\
       E[Γ] ⊢ f_1 : {(\kw{nil} ~\nat)}^P \\
       E[Γ] ⊢ f_2 : {(\kw{cons} ~\nat)}^P
     \end{array}
     ------------------------------------------------
     E[Γ] ⊢ \case(t,P,f_1 |f_2 ) : (P~t)


.. _Definition-of-ι-reduction:

**Definition of ι-reduction.**
We still have to define the ι-reduction in the general case.

An ι-redex is a term of the following form:

.. math::
   \case((c_{p_i}~q_1 … q_r~a_1 … a_m ),P,f_1 |… |f_l )
   
with :math:`c_{p_i}` the :math:`i`-th constructor of the inductive type :math:`I` with :math:`r`
parameters.

The ι-contraction of this term is :math:`(f_i~a_1 … a_m )` leading to the
general reduction rule:

.. math::
   \case((c_{p_i}~q_1 … q_r~a_1 … a_m ),P,f_1 |… |f_n ) \triangleright_ι (f_i~a_1 … a_m )


.. _Fixpoint-definitions:

Fixpoint definitions
~~~~~~~~~~~~~~~~~~~~

The second operator for elimination is fixpoint definition. This
fixpoint may involve several mutually recursive definitions. The basic
concrete syntax for a recursive set of mutually recursive declarations
is (with :math:`Γ_i` contexts):

.. math::
   \fix~f_1 (Γ_1 ) :A_1 :=t_1 \with … \with~f_n (Γ_n ) :A_n :=t_n


The terms are obtained by projections from this set of declarations
and are written

.. math::
   \fix~f_1 (Γ_1 ) :A_1 :=t_1 \with … \with~f_n (Γ_n ) :A_n :=t_n \for~f_i

In the inference rules, we represent such a term by

.. math::
   \Fix~f_i\{f_1 :A_1':=t_1' … f_n :A_n':=t_n'\}

with :math:`t_i'` (resp. :math:`A_i'`) representing the term :math:`t_i` abstracted (resp.
generalized) with respect to the bindings in the context Γ_i , namely
:math:`t_i'=λ Γ_i . t_i` and :math:`A_i'=∀ Γ_i , A_i`.


Typing rule
+++++++++++

The typing rule is the expected one for a fixpoint.

.. inference:: Fix
	       
   (E[Γ] ⊢ A_i : s_i )_{i=1… n}
   (E[Γ,f_1 :A_1 ,…,f_n :A_n ] ⊢ t_i : A_i )_{i=1… n}
   -------------------------------------------------------
   E[Γ] ⊢ \Fix~f_i\{f_1 :A_1 :=t_1 … f_n :A_n :=t_n \} : A_i


Any fixpoint definition cannot be accepted because non-normalizing
terms allow proofs of absurdity. The basic scheme of recursion that
should be allowed is the one needed for defining primitive recursive
functionals. In that case the fixpoint enjoys a special syntactic
restriction, namely one of the arguments belongs to an inductive type,
the function starts with a case analysis and recursive calls are done
on variables coming from patterns and representing subterms. For
instance in the case of natural numbers, a proof of the induction
principle of type

.. math::
   ∀ P:\nat→\Prop, (P~O)→(∀ n:\nat, (P~n)→(P~(\kw{S}~n)))→ ∀ n:\nat, (P~n)

can be represented by the term:

.. math::
   \begin{array}{l}
   λ P:\nat→\Prop. λ f:(P~O). λ g:(∀ n:\nat, (P~n)→(P~(S~n))).\\
   \Fix~h\{h:∀ n:\nat, (P~n):=λ n:\nat. \case(n,P,f | λp:\nat. (g~p~(h~p)))\}
   \end{array}

Before accepting a fixpoint definition as being correctly typed, we
check that the definition is “guarded”. A precise analysis of this
notion can be found in :cite:`Gim94`. The first stage is to precise on which
argument the fixpoint will be decreasing. The type of this argument
should be an inductive definition. For doing this, the syntax of
fixpoints is extended and becomes

.. math::
   \Fix~f_i\{f_1/k_1 :A_1':=t_1' … f_n/k_n :A_n':=t_n'\}


where :math:`k_i` are positive integers. Each :math:`k_i` represents the index of
parameter of :math:`f_i` , on which :math:`f_i` is decreasing. Each :math:`A_i` should be a
type (reducible to a term) starting with at least :math:`k_i` products
:math:`∀ y_1 :B_1 ,… ∀ y_{k_i} :B_{k_i} , A_i'` and :math:`B_{k_i}` an inductive type.

Now in the definition :math:`t_i`, if :math:`f_j` occurs then it should be applied to
at least :math:`k_j` arguments and the :math:`k_j`-th argument should be
syntactically recognized as structurally smaller than :math:`y_{k_i}`.

The definition of being structurally smaller is a bit technical. One
needs first to define the notion of *recursive arguments of a
constructor*. For an inductive definition :math:`\ind{r}{Γ_I}{Γ_C}`, if the
type of a constructor :math:`c` has the form
:math:`∀ p_1 :P_1 ,… ∀ p_r :P_r, ∀ x_1:T_1, … ∀ x_r :T_r, (I_j~p_1 … p_r~t_1 … t_s )`,
then the recursive
arguments will correspond to :math:`T_i` in which one of the :math:`I_l` occurs.

The main rules for being structurally smaller are the following.
Given a variable :math:`y` of an inductively defined type in a declaration
:math:`\ind{r}{Γ_I}{Γ_C}` where :math:`Γ_I` is :math:`[I_1 :A_1 ;…;I_k :A_k]`, and :math:`Γ_C` is
:math:`[c_1 :C_1 ;…;c_n :C_n ]`, the terms structurally smaller than :math:`y` are:


+ :math:`(t~u)` and :math:`λ x:u . t` when :math:`t` is structurally smaller than :math:`y`.
+ :math:`\case(c,P,f_1 … f_n)` when each :math:`f_i` is structurally smaller than :math:`y`.
  If :math:`c` is :math:`y` or is structurally smaller than :math:`y`, its type is an inductive
  definition :math:`I_p` part of the inductive declaration corresponding to :math:`y`.
  Each :math:`f_i` corresponds to a type of constructor
  :math:`C_q ≡ ∀ p_1 :P_1 ,…,∀ p_r :P_r , ∀ y_1 :B_1 , … ∀ y_k :B_k , (I~a_1 … a_k )`
  and can consequently be written :math:`λ y_1 :B_1' . … λ y_k :B_k'. g_i`. (:math:`B_i'` is
  obtained from :math:`B_i` by substituting parameters for variables) the variables
  :math:`y_j` occurring in :math:`g_i` corresponding to recursive arguments :math:`B_i` (the
  ones in which one of the :math:`I_l` occurs) are structurally smaller than y.


The following definitions are correct, we enter them using the :cmd:`Fixpoint`
command and show the internal representation.

.. example::

   .. coqtop:: all

      Fixpoint plus (n m:nat) {struct n} : nat :=
      match n with
      | O => m
      | S p => S (plus p m)
      end.

      Print plus.
      Fixpoint lgth (A:Set) (l:list A) {struct l} : nat :=
      match l with
      | nil _ => O
      | cons _ a l' => S (lgth A l')
      end.
      Print lgth.
      Fixpoint sizet (t:tree) : nat := let (f) := t in S (sizef f)
      with sizef (f:forest) : nat :=
      match f with
      | emptyf => O
      | consf t f => plus (sizet t) (sizef f)
      end.
      Print sizet.

.. _Reduction-rule:

Reduction rule
++++++++++++++

Let :math:`F` be the set of declarations:
:math:`f_1 /k_1 :A_1 :=t_1 …f_n /k_n :A_n:=t_n`.
The reduction for fixpoints is:

.. math::
   (\Fix~f_i \{F\} a_1 …a_{k_i}) \triangleright_ι \subst{t_i}{f_k}{\Fix~f_k \{F\}}_{k=1… n} ~a_1 … a_{k_i}
   
when :math:`a_{k_i}` starts with a constructor. This last restriction is needed
in order to keep strong normalization and corresponds to the reduction
for primitive recursive operators. The following reductions are now
possible:

.. math::
   :nowrap:

   {\def\plus{\mathsf{plus}}
    \def\tri{\triangleright_\iota}
    \begin{eqnarray*}
    \plus~(\nS~(\nS~\nO))~(\nS~\nO) & \tri & \nS~(\plus~(\nS~\nO)~(\nS~\nO))\\
                                   & \tri & \nS~(\nS~(\plus~\nO~(\nS~\nO)))\\
                                   & \tri & \nS~(\nS~(\nS~\nO))\\
    \end{eqnarray*}}

.. _Mutual-induction:

**Mutual induction**

The principles of mutual induction can be automatically generated
using the Scheme command described in Section :ref:`proofschemes-induction-principles`.


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
the constant :math:`c'`.

Below, if :math:`Γ` is a context of the form :math:`[y_1 :A_1 ;…;y_n :A_n]`, we write
:math:`∀x:U,\subst{Γ}{c}{x}` to mean
:math:`[y_1 :∀ x:U,\subst{A_1}{c}{x};…;y_n :∀ x:U,\subst{A_n}{c}{x}]`
and :math:`\subst{E}{|Γ|}{|Γ|c}` to mean the parallel substitution
:math:`E\{y_1 /(y_1~c)\}…\{y_n/(y_n~c)\}`.


.. _First-abstracting-property:

**First abstracting property:**

.. math::
   \frac{\WF{E;c:U;E′;c′:=t:T;E″}{Γ}}
        {\WF{E;c:U;E′;c′:=λ x:U. \subst{t}{c}{x}:∀x:U,\subst{T}{c}{x};\subst{E″}{c′}{(c′~c)}}
	{\subst{Γ}{c}{(c~c′)}}}

   
.. math::
   \frac{\WF{E;c:U;E′;c′:T;E″}{Γ}}
        {\WF{E;c:U;E′;c′:∀ x:U,\subst{T}{c}{x};\subst{E″}{c′}{(c′~c)}}{Γ{c/(c~c′)}}}
	
.. math::
   \frac{\WF{E;c:U;E′;\ind{p}{Γ_I}{Γ_C};E″}{Γ}}
        {\WFTWOLINES{E;c:U;E′;\ind{p+1}{∀ x:U,\subst{Γ_I}{c}{x}}{∀ x:U,\subst{Γ_C}{c}{x}};
	  \subst{E″}{|Γ_I ,Γ_C |}{|Γ_I ,Γ_C | c}}
	 {\subst{Γ}{|Γ_I ,Γ_C|}{|Γ_I ,Γ_C | c}}}

One can similarly modify a global declaration by generalizing it over
a previously defined constant :math:`c′`. Below, if :math:`Γ` is a context of the form
:math:`[y_1 :A_1 ;…;y_n :A_n]`, we write :math:`\subst{Γ}{c}{u}` to mean
:math:`[y_1 :\subst{A_1} {c}{u};…;y_n:\subst{A_n} {c}{u}]`.


.. _Second-abstracting-property:

**Second abstracting property:**

.. math::
   \frac{\WF{E;c:=u:U;E′;c′:=t:T;E″}{Γ}}
        {\WF{E;c:=u:U;E′;c′:=(\letin{x}{u:U}{\subst{t}{c}{x}}):\subst{T}{c}{u};E″}{Γ}}

.. math::
   \frac{\WF{E;c:=u:U;E′;c′:T;E″}{Γ}}
        {\WF{E;c:=u:U;E′;c′:\subst{T}{c}{u};E″}{Γ}}

.. math::
   \frac{\WF{E;c:=u:U;E′;\ind{p}{Γ_I}{Γ_C};E″}{Γ}}
        {\WF{E;c:=u:U;E′;\ind{p}{\subst{Γ_I}{c}{u}}{\subst{Γ_C}{c}{u}};E″}{Γ}}

.. _Pruning-the-local-context:

**Pruning the local context.**
If one abstracts or substitutes constants with the above rules then it
may happen that some declared or defined constant does not occur any
more in the subsequent global environment and in the local context.
One can consequently derive the following property.


.. _First-pruning-property:

.. inference:: First pruning property:
	       
   \WF{E;c:U;E′}{Γ}
   c~\kw{does not occur in}~E′~\kw{and}~Γ
   --------------------------------------
   \WF{E;E′}{Γ}


.. _Second-pruning-property:

.. inference:: Second pruning property:

   \WF{E;c:=u:U;E′}{Γ}
   c~\kw{does not occur in}~E′~\kw{and}~Γ
   --------------------------------------
   \WF{E;E′}{Γ}


.. _Co-inductive-types:

Co-inductive types
----------------------

The implementation contains also co-inductive definitions, which are
types inhabited by infinite objects. More information on co-inductive
definitions can be found in :cite:`Gimenez95b,Gim98,GimCas05`.


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
   s ∈ {\Sort}
   E[Γ::(x:T)] ⊢ U : Set
   ---------------------
   E[Γ] ⊢ ∀ x:T,U : Set

This extension has consequences on the inductive definitions which are
allowed. In the impredicative system, one can build so-called *large
inductive definitions* like the example of second-order existential
quantifier (:g:`exSet`).

There should be restrictions on the eliminations which can be
performed on such definitions. The elimination rules in the
impredicative system for sort :math:`\Set` become:



.. inference:: Set1

   s ∈ \{Prop, Set\}
   -----------------
   [I:Set|I→ s]

.. inference:: Set2

   I~\kw{is a small inductive definition}
   s ∈ \{\Type(i)\}
   ----------------
   [I:Set|I→ s]


