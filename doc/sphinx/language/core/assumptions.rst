Functions and assumptions
=========================

.. _binders:

Binders
-------

.. insertprodn open_binders binder

.. prodn::
   open_binders ::= {+ @name } : @term
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
   term_forall_or_fun ::= forall @open_binders , @term
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

The expression :n:`forall @ident : @type, @term` denotes the
*product* of the variable :n:`@ident` of type :n:`@type`, over the term :n:`@term`.
As for abstractions, :g:`forall` is followed by a binder list, and products
over several variables are equivalent to an iteration of one-variable
products. Note that :n:`@term` is intended to be a type.

If the variable :n:`@ident` occurs in :n:`@term`, the product is called
*dependent product*. The intention behind a dependent product
:g:`forall x : A, B` is twofold. It denotes either
the universal quantification of the variable :g:`x` of type :g:`A`
in the proposition :g:`B` or the functional dependent product from
:g:`A` to :g:`B` (a construction usually written
:math:`\Pi_{x:A}.B` in set theory).

Non dependent product types have a special notation: :g:`A -> B` stands for
:g:`forall _ : A, B`. The *non dependent product* is used both to denote
the propositional implication and function types.

Function application
--------------------

.. insertprodn term_application arg

.. prodn::
   term_application ::= @term1 {+ @arg }
   | @ @qualid_annotated {+ @term1 }
   arg ::= ( @ident := @term )
   | @term1

:n:`@term__fun @term` denotes applying the function :n:`@term__fun` to :token:`term`.

:n:`@term__fun {+ @term__i }` denotes applying
:n:`@term__fun` to the arguments :n:`@term__i`.  It is
equivalent to :n:`( … ( @term__fun @term__1 ) … ) @term__n`:
associativity is to the left.

The notation :n:`(@ident := @term)` for arguments is used for making
explicit the value of implicit arguments (see
Section :ref:`explicit-applications`).

.. _gallina-assumptions:

Assumptions
-----------

Assumptions extend the environment with axioms, parameters, hypotheses
or variables. An assumption binds an :n:`@ident` to a :n:`@type`. It is accepted
by Coq if and only if this :n:`@type` is a correct type in the environment
preexisting the declaration and if :n:`@ident` was not previously defined in
the same module. This :n:`@type` is considered to be the type (or
specification, or statement) assumed by :n:`@ident` and we say that :n:`@ident`
has type :n:`@type`.

.. _Axiom:

.. cmd:: @assumption_token {? Inline {? ( @num ) } } {| {+ ( @assumpt ) } | @assumpt }
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
      of_type ::= {| : | :> | :>> } @type

   These commands bind one or more :n:`@ident`\(s) to specified :n:`@type`\(s) as their specifications in
   the global context. The fact asserted by the :n:`@type` (or, equivalently, the existence
   of an object of this type) is accepted as a postulate.

   :cmd:`Axiom`, :cmd:`Conjecture`, :cmd:`Parameter` and their plural forms
   are equivalent.  They can take the :attr:`local` :term:`attribute`,
   which makes the defined :n:`@ident`\s accessible by :cmd:`Import` and its variants
   only through their fully qualified names.

   Similarly, :cmd:`Hypothesis`, :cmd:`Variable` and their plural forms are equivalent.  Outside
   of a section, these are equivalent to :n:`Local Parameter`.  Inside a section, the
   :n:`@ident`\s defined are only accessible within the section.  When the current section
   is closed, the :n:`@ident`\(s) become undefined and every object depending on them will be explicitly
   parameterized (i.e., the variables are *discharged*).  See Section :ref:`section-mechanism`.

   The :n:`Inline` clause is only relevant inside functors.  See :cmd:`Module`.

.. example:: Simple assumptions

    .. coqtop:: reset in

       Parameter X Y : Set.
       Parameter (R : X -> Y -> Prop) (S : Y -> X -> Prop).
       Axiom R_S_inv : forall x y, R x y <-> S y x.

.. exn:: @ident already exists.
   :name: @ident already exists. (Axiom)
   :undocumented:

.. warn:: @ident is declared as a local axiom

   Warning generated when using :cmd:`Variable` or its equivalent
   instead of :n:`Local Parameter` or its equivalent.

.. note::
   We advise using the commands :cmd:`Axiom`, :cmd:`Conjecture` and
   :cmd:`Hypothesis` (and their plural forms) for logical postulates (i.e. when
   the assertion :n:`@type` is of sort :g:`Prop`), and to use the commands
   :cmd:`Parameter` and :cmd:`Variable` (and their plural forms) in other cases
   (corresponding to the declaration of an abstract object of the given type).
