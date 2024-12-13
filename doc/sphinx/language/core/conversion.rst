.. _Conversion-rules:

Conversion rules
----------------

The Rocq Prover has conversion rules that can be used to determine if two
terms are equal by definition in |CiC|, or :term:`convertible`.
Conversion rules consist of reduction rules and expansion rules.
Equality is determined by
converting both terms to a normal form, then verifying they are syntactically
equal (ignoring differences in the names of bound variables by
:term:`alpha-conversion <alpha-convertible>`).

.. seealso:: :ref:`applyingconversionrules`, which describes tactics that apply these conversion rules.

:gdef:`Reductions <reduction>` convert terms to something that is incrementally
closer to its normal form.  For example, :term:`zeta-reduction` removes
:n:`let @ident := @term__1 in @term__2` constructs from a term by replacing
:n:`@ident` with :n:`@term__1` wherever :n:`@ident` appears in :n:`@term__2`.
The resulting term may be longer or shorter than the original.

.. rocqtop:: all

   Eval cbv zeta in let i := 1 in i + i.

:gdef:`Expansions <expansion>` are reductions applied in the opposite direction,
for example expanding `2 + 2` to `let i := 2 in i + i`.  While applying
reductions gives a unique result, the associated
expansion may not be unique.  For example, `2 + 2` could also be
expanded to `let i := 2 in i + 2`.  Reductions that have a unique inverse
expansion are also referred to as :gdef:`contractions <contraction>`.

The normal form is defined as the result of applying a particular
set of conversion rules (beta-, delta-, iota- and zeta-reduction and eta-expansion)
repeatedly until it's no longer possible to apply any of them.

Sometimes the result of a reduction tactic will be a simple value, for example reducing
`2*3+4` with `cbv beta delta iota` to `10`, which requires applying several
reduction rules repeatedly.  In other cases, it may yield an expression containing
variables, axioms or opaque contants that can't be reduced.

The useful conversion rules are shown below.  All of them except for eta-expansion
can be applied with conversion tactics such as :tacn:`cbv`:

   .. list-table::
      :header-rows: 1

      * - Conversion name
        - Description

      * - beta-reduction
        - eliminates `fun`

      * - delta-reduction
        - replaces a defined variable or constant with its definition

      * - zeta-reduction
        - eliminates `let`

      * - eta-expansion
        - replaces a term `f` of type `forall a : A, B` with `fun x : A => f x`

      * - match-reduction
        - eliminates `match`

      * - fix-reduction
        - replaces a `fix` with a :term:`beta-redex`;
          recursive calls to the symbol are replaced with the `fix` term

      * - cofix-reduction
        - replaces a `cofix` with a :term:`beta-redex`;
          recursive calls to the symbol are replaced with the `cofix` term

      * - iota-reduction
        - match-, fix- and cofix-reduction together

:ref:`applyingconversionrules`
describes tactics that only apply conversion rules.
(Other tactics may use conversion rules in addition
to other changes to the proof state.)

α-conversion
~~~~~~~~~~~~

Two terms are :gdef:`α-convertible <alpha-convertible>` if they are syntactically
equal ignoring differences in the names of variables bound within the expression.
For example `forall x, x + 0 = x` is α-convertible with `forall y, y + 0 = y`.
(Internally, Rocq represents these two terms using de Bruijn indices,
so explicit α-conversion is not necessary.)

β-reduction
~~~~~~~~~~~

:gdef:`β-reduction <beta-reduction>` reduces a :gdef:`beta-redex`, which is
a term in the form `(fun x => t) u`.  (Beta-redex
is short for "beta-reducible expression", a term from lambda calculus.
See `Beta reduction <https://en.wikipedia.org/wiki/Beta_normal_form#Beta_reduction>`_
for more background.)

Formally, in any :term:`global environment` :math:`E` and :term:`local context`
:math:`Γ`, the beta-reduction rule is:

.. inference:: Beta

   --------------
   E[Γ] ⊢ ((λx:T.~t)~u)~\triangleright_β~\subst{t}{x}{u}

We say that :math:`\subst{t}{x}{u}` is the *β-contraction* of
:math:`((λx:T.~t)~u)` and, conversely, that :math:`((λ x:T.~t)~u)` is the
*β-expansion* of :math:`\subst{t}{x}{u}`.

.. todo: :term:`Calculus of Inductive Constructions` fails to build in CI for some reason :-()

Terms of the *Calculus of Inductive Constructions*
enjoy some fundamental properties such as confluence,
strong normalization, subject reduction. These results are
theoretically of great importance but we will not detail them here and
refer the interested reader to :cite:`Coq85`.

.. _delta-reduction-sect:

δ-reduction
~~~~~~~~~~~

:gdef:`δ-reduction <delta-reduction>` replaces variables defined in
:term:`local contexts <local context>`
or :term:`constants <constant>` defined in the :term:`global environment` with their values.
:gdef:`Unfolding <unfold>` means to replace a constant by its definition. Formally, this is:

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

:term:`Delta-reduction <delta-reduction>` only unfolds :term:`constants <constant>` that are
marked :gdef:`transparent`.  :gdef:`Opaque <opaque>` is the opposite of
transparent; :term:`delta-reduction` doesn't unfold opaque constants.

ι-reduction
~~~~~~~~~~~

A specific conversion rule is associated with the inductive objects in
the global environment. We shall give later on (see Section
:ref:`Well-formed-inductive-definitions`) the precise rules but it
just says that a destructor applied to an object built from a
constructor behaves as expected. This reduction is called
:gdef:`ι-reduction <iota-reduction>`
and is more precisely studied in :cite:`Moh93,Wer94`.

ζ-reduction
~~~~~~~~~~~

:gdef:`ζ-reduction <zeta-reduction>` removes :ref:`let-in definitions <let-in>`
in terms by
replacing the defined variable by its value. One way this reduction differs from
δ-reduction is that the declaration is removed from the term entirely.
Formally, this is:

.. inference:: Zeta

   \WFE{\Gamma}
   \WTEG{u}{U}
   \WTE{\Gamma::(x:=u:U)}{t}{T}
   --------------
   E[Γ] ⊢ \letin{x}{u:U}{t}~\triangleright_ζ~\subst{t}{x}{u}


.. _eta-expansion-sect:

η-expansion
~~~~~~~~~~~

Another important concept is :gdef:`η-expansion <eta-expansion>`. It is legal to identify any
term :math:`t` of functional type :math:`∀ x:T,~U` with its so-called η-expansion

.. math::
   λx:T.~(t~x)

for :math:`x` an arbitrary variable name fresh in :math:`t`.


.. note::

   We deliberately do not define η-reduction:

   .. math::
      λ x:T.~(t~x)~\not\triangleright_η~t

   This is because, in general, the type of :math:`t` need not be convertible
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

Examples
~~~~~~~~

   .. example:: Simple delta, fix, beta and match reductions

      ``+`` is a :ref:`notation <Notations>` for ``Nat.add``, which is defined
      with a :cmd:`Fixpoint`.

      .. rocqtop:: all abort

         Print Nat.add.
         Goal 1 + 1 = 2.
         cbv delta.
         cbv fix.
         cbv beta.
         cbv match.

      The term can be fully reduced with `cbv`:

      .. rocqtop:: all abort

         Goal 1 + 1 = 2.
         cbv.

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
*βδιζη-convertible*, or simply :gdef:`convertible`, or
:term:`definitionally equal <definitional equality>`, in the
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
