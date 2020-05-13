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
instance the identity function over a given type :math:`T` can be written
:math:`λx:T.~x`. In any global environment :math:`E` and local context
:math:`Γ`, we want to identify any object :math:`a` (of type
:math:`T`) with the application :math:`((λ x:T.~x)~a)`.  We define for
this a *reduction* (or a *conversion*) rule we call :math:`β`:

.. math::

        E[Γ] ⊢ ((λx:T.~t)~u)~\triangleright_β~\subst{t}{x}{u}

We say that :math:`\subst{t}{x}{u}` is the *β-contraction* of
:math:`((λx:T.~t)~u)` and, conversely, that :math:`((λ x:T.~t)~u)` is the
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
   E[Γ] ⊢ \letin{x}{u:U}{t}~\triangleright_ζ~\subst{t}{x}{u}


.. _eta-expansion:

η-expansion
~~~~~~~~~~~

Another important concept is η-expansion. It is legal to identify any
term :math:`t` of functional type :math:`∀ x:T,~U` with its so-called η-expansion

.. math::
   λx:T.~(t~x)

for :math:`x` an arbitrary variable name fresh in :math:`t`.


.. note::

   We deliberately do not define η-reduction:

   .. math::
      λ x:T.~(t~x)~\not\triangleright_η~t

   This is because, in general, the type of :math:`t` need not to be convertible
   to the type of :math:`λ x:T.~(t~x)`. E.g., if we take :math:`f` such that:

   .. math::
      f ~:~ ∀ x:\Type(2),~\Type(1)

   then

   .. math::
      λ x:\Type(1).~(f~x) ~:~ ∀ x:\Type(1),~\Type(1)

   We could not allow

   .. math::
      λ x:\Type(1).~(f~x) ~\triangleright_η~ f

   because the type of the reduced term :math:`∀ x:\Type(2),~\Type(1)` would not be
   convertible to the type of the original term :math:`∀ x:\Type(1),~\Type(1)`.

.. _proof-irrelevance:

Proof Irrelevance
~~~~~~~~~~~~~~~~~

It is legal to identify any two terms whose common type is a strict
proposition :math:`A : \SProp`. Terms in a strict propositions are
therefore called *irrelevant*.

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
:math:`u_2` are identical up to irrelevant subterms, or they are convertible up to η-expansion,
i.e. :math:`u_1` is :math:`λ x:T.~u_1'` and :math:`u_2 x` is
recursively convertible to :math:`u_1'`, or, symmetrically,
:math:`u_2` is :math:`λx:T.~u_2'`
and :math:`u_1 x` is recursively convertible to :math:`u_2'`. We then write
:math:`E[Γ] ⊢ t_1 =_{βδιζη} t_2`.

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
