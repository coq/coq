Functions and assumptions
=========================

.. _binders:

Binders
-------

.. insertprodn open_binders binder

.. prodn::
   open_binders ::= {+ @name } : @type
   | {+ @binder }
   name ::= _
   | @ident
   binder ::= @name
   | ( {+ @name } : @type )
   | ( @name {? : @type } := @term )
   | @implicit_binders
   | @generalizing_binder
   | ( @name : @type %| @term )
   | ' @pattern0

Various constructions such as :g:`fun`, :g:`forall`, :g:`fix` and :g:`cofix`
*bind* variables. A binding is represented by an identifier. If the binding
variable is not used in the expression, the identifier can be replaced by the
symbol :g:`_`. When the type of a bound variable cannot be synthesized by the
system, it can be specified with the notation :n:`(@ident : @type)`. There is also
a notation for a sequence of binding variables sharing the same type:
:n:`({+ @ident} : @type)`. A
binder can also be any pattern prefixed by a quote, e.g. :g:`'(x,y)`.

Some constructions allow the binding of a variable to value. This is
called a “let-binder”. The entry :n:`@binder` of the grammar accepts
either an assumption binder as defined above or a let-binder. The notation in
the latter case is :n:`(@ident := @term)`. In a let-binder, only one
variable can be introduced at the same time. It is also possible to give
the type of the variable as follows:
:n:`(@ident : @type := @term)`.

`(x : T | P)` is syntactic sugar for `(x : @Stdlib.Init.Specif.sig _ (fun x : T => P))`,
which would more typically be written `(x : {x : T | P})`.
Since `(x : T | P)` uses `sig` directly,
changing the notation `{x : T | P}`
will not change the meaning of `(x : T | P)`.

Lists of :n:`@binder`\s are allowed. In the case of :g:`fun` and :g:`forall`,
it is intended that at least one binder of the list is an assumption otherwise
fun and forall gets identical. Moreover, parentheses can be omitted in
the case of a single sequence of bindings sharing the same type (e.g.:
:g:`fun (x y z : A) => t` can be shortened in :g:`fun x y z : A => t`).

.. index:: fun
.. index:: forall

Functions (fun) and function types (forall)
-------------------------------------------

.. insertprodn term_forall_or_fun term_forall_or_fun

.. prodn::
   term_forall_or_fun ::= forall @open_binders , @type
   | fun @open_binders => @term

The expression :n:`fun @ident : @type => @term` defines the
*abstraction* of the variable :n:`@ident`, of type :n:`@type`, over the term
:n:`@term`. It denotes a function of the variable :n:`@ident` that evaluates to
the expression :n:`@term` (e.g. :g:`fun x : A => x` denotes the identity
function on type :g:`A`). The keyword :g:`fun` can be followed by several
binders as given in Section :ref:`binders`. Functions over
several variables are equivalent to an iteration of one-variable
functions. For instance the expression
:n:`fun {+ @ident__i } : @type => @term`
denotes the same function as :n:`{+ fun @ident__i : @type => } @term`. If
a let-binder occurs in
the list of binders, it is expanded to a let-in definition (see
Section :ref:`let-in`).

The expression :n:`forall @ident : @type__1, @type__2` denotes the
:gdef:`product type <product>` (or *product*) of the variable :n:`@ident` of
type :n:`@type__1` over the type :n:`@type__2`.  If :n:`@ident` is used in
:n:`@type__2`, then we say the expression is a :gdef:`dependent product`,
and otherwise a :gdef:`non-dependent product`.

The intention behind a dependent product
:g:`forall x : A, B` is twofold. It denotes either
the universal quantification of the variable :g:`x` of type :g:`A`
in the proposition :g:`B` or the functional dependent product from
:g:`A` to :g:`B` (a construction usually written
:math:`\Pi_{x:A}.B` in set theory).

Non-dependent product types have a special notation: :g:`A -> B` stands for
:g:`forall _ : A, B`. *Non-dependent product* is used to denote both
propositional implication and function types.

These terms are also useful:

* `n : nat` is a :gdef:`dependent premise` of `forall n:nat, n + 0 = n` because
  `n` appears both in the binder of the `forall` and in the quantified statement
  `n + 0 = n`.  Note that if `n` isn't used in the statement, Rocq considers it
  a non-dependent premise.  Similarly, :n:`let n := ... in @term` is a
  dependent premise only if `n` is used in :n:`@term`.

* `A` and `B` are :gdef:`non-dependent premises <non-dependent premise>`
  (or, often, just ":gdef:`premises <premise>`") of `A -> B -> C` because they don't appear
  in a `forall` binder.  `C` is the *conclusion* of the type, which is a second
  meaning for the term :term:`conclusion`.
  (As noted, `A -> B` is notation for the term `forall _ : A, B`; the wildcard
  `_` can't be referred to in the quantified statement.)

As for abstractions, :g:`forall` is followed by a binder list, and products
over several variables are equivalent to an iteration of one-variable
products.

.. _function_application:

Function application
--------------------

.. insertprodn term_application arg

.. prodn::
   term_application ::= @term1 {+ @arg }
   | @ @qualid_annotated {+ @term1 }
   arg ::= ( @ident := @term )
   | ( @natural := @term )
   | @term1

:n:`@term1__fun @term1` denotes applying the function :n:`@term1__fun` to :token:`term1`.

.. todo: What is the relevant definition of a function here?
         See https://github.com/coq/coq/pull/16659#discussion_r1039540851

:n:`@term1__fun {+ @term1__i }` denotes applying
:n:`@term1__fun` to the arguments :n:`@term1__i`.  It is
equivalent to :n:`( … ( @term1__fun @term1__1 ) … ) @term1__n`:
associativity is to the left.

The :n:`@ @qualid_annotated {+ @term1 }` form requires specifying all arguments,
including implicit ones.  Otherwise, implicit arguments need
not be given.  See :ref:`ImplicitArguments`.

The notations :n:`(@ident := @term)` and :n:`(@natural := @term)`
for arguments are used for making explicit the value of implicit arguments.
See :ref:`explicit-applications`.

.. _gallina-assumptions:

Assumptions
-----------

Assumptions extend the global environment with axioms, parameters, hypotheses
or variables. An assumption binds an :n:`@ident` to a :n:`@type`. It is accepted
by Rocq only if :n:`@type` is a correct type in the global environment
before the declaration and if :n:`@ident` was not previously defined in
the same module. This :n:`@type` is considered to be the type (or
specification, or statement) assumed by :n:`@ident` and we say that :n:`@ident`
has type :n:`@type`.

.. _Axiom:

.. cmd:: @assumption_token {? Inline {? ( @natural ) } } {| @assumpt | {+ ( @assumpt ) } }
   :name: Axiom; Axioms; Conjecture; Conjectures; Hypothesis; Hypotheses; Parameter; Parameters; Variable; Variables

   .. insertprodn assumption_token of_type

   .. prodn::
      assumption_token ::= {| Axiom | Axioms }
      | {| Conjecture | Conjectures }
      | {| Parameter | Parameters }
      | {| Hypothesis | Hypotheses }
      | {| Variable | Variables }
      assumpt ::= {+ @ident_decl } @of_type
      ident_decl ::= @ident {? @univ_decl }
      of_type ::= {| : | :> } @type

   These commands bind one or more :n:`@ident`\(s) to specified :n:`@type`\(s) as their specifications in
   the global environment. The fact asserted by :n:`@type` (or, equivalently, the existence
   of an object of this type) is accepted as a postulate.  They accept the :attr:`program`,
   :attr:`deprecated` and :attr:`warn` attributes.

   :cmd:`Axiom`, :cmd:`Conjecture`, :cmd:`Parameter` and their plural forms
   are equivalent.  They can take the :attr:`local` :term:`attribute`,
   which makes the declared :n:`@ident` accessible only through their fully
   qualified names, even if :cmd:`Import` or its variants has been used on the
   current module.

   which makes the defined :n:`@ident`\s accessible by :cmd:`Import` and its variants
   only through their fully qualified names.

   Similarly, :cmd:`Hypothesis`, :cmd:`Variable` and their plural forms are equivalent.
   They should only be used inside :ref:`section-mechanism`. The
   :n:`@ident`\s defined are only accessible within the section.  When the current section
   is closed, the :n:`@ident`\(s) become undefined and every object depending on them will be explicitly
   parameterized (i.e., the variables are *discharged*).  See Section :ref:`section-mechanism`.

   :n:`:>`
     If specified, :token:`ident_decl` is automatically
     declared as a coercion to the class of its type.  See :ref:`coercions`.

   The :n:`Inline` clause is only relevant inside functors.  See :cmd:`Module`.

.. example:: Simple assumptions

    .. rocqtop:: reset in

       Parameter X Y : Set.
       Parameter (R : X -> Y -> Prop) (S : Y -> X -> Prop).
       Axiom R_S_inv : forall x y, R x y <-> S y x.

.. exn:: @ident already exists.
   :name: ‘ident’ already exists. (Axiom)
   :undocumented:

.. warn:: Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter" or "#[local] Axiom".

   Warning generated when using :cmd:`Variable` or its equivalent
   instead of :n:`Local Parameter` or its equivalent.
   This message is an error by default, it may be convenient to disable it
   while debuging.

.. note::
   We advise using the commands :cmd:`Axiom`, :cmd:`Conjecture` and
   :cmd:`Hypothesis` (and their plural forms) for logical postulates (i.e. when
   the assertion :n:`@type` is of sort :g:`Prop`), and to use the commands
   :cmd:`Parameter` and :cmd:`Variable` (and their plural forms) in other cases
   (corresponding to the declaration of an abstract object of the given type).
