.. _ArgumentsCommand:

Setting properties of a function's arguments
++++++++++++++++++++++++++++++++++++++++++++

.. cmd:: Arguments @smart_global {* @arg_specs } {* , {* @implicits_alt } } {? : {+, @args_modifier } }
   :name: Arguments

   .. insertprodn argument_spec args_modifier

   .. prodn::
      argument_spec ::= {? ! } @name {? % @scope_key }
      arg_specs ::= @argument_spec
      | /
      | &
      | ( {+ @argument_spec } ) {? % @scope_key }
      | [ {+ @argument_spec } ] {? % @scope_key }
      | %{ {+ @argument_spec } %} {? % @scope_key }
      implicits_alt ::= @name
      | [ {+ @name } ]
      | %{ {+ @name } %}
      args_modifier ::= simpl nomatch
      | simpl never
      | default implicits
      | clear implicits
      | clear scopes
      | clear bidirectionality hint
      | rename
      | assert
      | extra scopes
      | clear scopes and implicits
      | clear implicits and scopes

   Specifies properties of the arguments of a function after the function has already
   been defined.  It gives fine-grained
   control over the elaboration process (i.e. the translation of Gallina language
   extensions into the core language used by the kernel).  The command's effects include:

   * Making arguments implicit. Afterward, implicit arguments
     must be omitted in any expression that applies :token:`smart_global`.
   * Declaring that some arguments of a given function should
     be interpreted in a given scope.
   * Affecting when the :tacn:`simpl` and :tacn:`cbn` tactics unfold the function.
     See :ref:`Args_effect_on_unfolding`.
   * Providing bidirectionality hints.  See :ref:`bidirectionality_hints`.

   This command supports the :attr:`local` and :attr:`global` attributes.
   Default behavior is to limit the effect to the current section but also to
   extend their effect outside the current module or library file.
   Applying :attr:`local` limits the effect of the command to the current module if
   it's not in a section.  Applying :attr:`global` within a section extends the
   effect outside the current sections and current module in which the command appears.

      `/`
         the function will be unfolded only if it's applied to at least the
         arguments appearing before the `/`.  See :ref:`Args_effect_on_unfolding`.

         .. exn:: The / modifier may only occur once.
            :undocumented:

      `&`
         tells the type checking algorithm to first type check the arguments
         before the `&` and then to propagate information from that typing context
         to type check the remaining arguments. See :ref:`bidirectionality_hints`.

         .. exn:: The & modifier may only occur once.
            :undocumented:

      :n:`( ... ) {? % @scope }`
         :n:`(@name__1 @name__2 ...)%@scope` is shorthand for :n:`@name__1%@scope @name__2%@scope ...`

      :n:`[ ... ] {? % @scope }`
         declares the enclosed names as implicit, non-maximally inserted.
         :n:`[@name__1 @name__2 ... ]%@scope` is equivalent to :n:`[@name__1]%@scope [@name__2]%@scope ...`

      :n:`%{ ... %} {? % @scope }`
         declares the enclosed names as implicit, maximally inserted.
         :n:`%{@name__1 @name__2 ... %}%@scope` is equivalent to :n:`%{@name__1%}%@scope %{@name__2%}%@scope ...`

      `!`
         the function will be unfolded only if all the arguments marked with `!`
         evaulate to constructors.  See :ref:`Args_effect_on_unfolding`.

      :n:`@name {? % @scope }`
         a *formal parameter* of the function :n:`@smart_global` (i.e.
         the parameter name used in the function definition).  Unless `rename` is specified,
         the list of :n:`@name`\s must be a prefix of the formal parameters, including all implicit
         arguments.  `_` can be used to skip over a formal parameter.
         :token:`scope` can be either a scope name or its delimiting key.  See :ref:`binding_to_scope`.

      `clear implicits`
         makes all implicit arguments into explicit arguments
      `default implicits`
         automatically determine the implicit arguments of the object.
         See :ref:`auto_decl_implicit_args`.
      `rename`
         rename implicit arguments for the object.  See the example :ref:`here <renaming_implicit_arguments>`.
      `assert`
         assert that the object has the expected number of arguments with the
         expected names.  See the example here: :ref:`renaming_implicit_arguments`.

         .. warn:: This command is just asserting the names of arguments of @qualid. If this is what you want, add ': assert' to silence the warning. If you want to clear implicit arguments, add ': clear implicits'. If you want to clear notation scopes, add ': clear scopes'
            :undocumented:

      `clear scopes`
         clears argument scopes of :n:`@smart_global`
      `extra scopes`
         defines extra argument scopes, to be used in case of coercion to ``Funclass``
         (see :ref:`coercions`) or with a computed type.
      `simpl nomatch`
         prevents performing a simplification step for :n:`@smart_global`
         that would expose a match construct in the head position.  See :ref:`Args_effect_on_unfolding`.
      `simpl never`
         prevents performing a simplification step for :n:`@smart_global`.  See :ref:`Args_effect_on_unfolding`.

      `clear bidirectionality hint`
         removes the bidirectionality hint, the `&`

      :n:`@implicits_alt`
         use to specify alternative implicit argument declarations
         for functions that can only be
         applied to a fixed number of arguments (excluding, for instance,
         functions whose type is polymorphic).
         For parsing, the longest list of implicit arguments matching the function application
         is used to select which implicit arguments are inserted.
         For printing, the alternative with the most implicit arguments is used; the
         implict arguments will be omitted if :flag:`Printing Implicit` is not set.
         See the example :ref:`here<example_more_implicits>`.

         .. todo the above feature seems a bit unnatural and doesn't play well with partial
            application.  See https://github.com/coq/coq/pull/11718#discussion_r408841762

   Use :cmd:`About` to view the current implicit arguments setting for a :token:`smart_global`.

   Or use the :cmd:`Print Implicit` command to see the implicit arguments
   of an object (see :ref:`displaying-implicit-args`).

Manual declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example::

   .. coqtop:: reset all

      Inductive list (A : Type) : Type :=
      | nil : list A
      | cons : A -> list A -> list A.

      Check (cons nat 3 (nil nat)).

      Arguments cons [A] _ _.

      Arguments nil {A}.

      Check (cons 3 nil).

      Fixpoint map (A B : Type) (f : A -> B) (l : list A) : list B :=
        match l with nil => nil | cons a t => cons (f a) (map A B f t) end.

      Fixpoint length (A : Type) (l : list A) : nat :=
        match l with nil => 0 | cons _ m => S (length A m) end.

      Arguments map [A B] f l.

      Arguments length {A} l. (* A has to be maximally inserted *)

      Check (fun l:list (list nat) => map length l).

.. _example_more_implicits:

.. example:: Multiple alternatives with :n:`@implicits_alt`

   .. coqtop:: all

      Arguments map [A B] f l, [A] B f l, A B f l.

      Check (fun l => map length l = map (list nat) nat length l).

.. _auto_decl_implicit_args:

Automatic declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The ":n:`default implicits`" :token:`args_modifier` clause tells |Coq| to automatically determine the
   implicit arguments of the object.

   Auto-detection is governed by flags specifying whether strict,
   contextual, or reversible-pattern implicit arguments must be
   considered or not (see :ref:`controlling-strict-implicit-args`, :ref:`controlling-contextual-implicit-args`,
   :ref:`controlling-rev-pattern-implicit-args` and also :ref:`controlling-insertion-implicit-args`).

.. example:: Default implicits

   .. coqtop:: reset all

      Inductive list (A:Set) : Set :=
      | nil : list A
      | cons : A -> list A -> list A.

      Arguments cons : default implicits.

      Print Implicit cons.

      Arguments nil : default implicits.

      Print Implicit nil.

      Set Contextual Implicit.

      Arguments nil : default implicits.

      Print Implicit nil.

The computation of implicit arguments takes account of the unfolding
of constants. For instance, the variable ``p`` below has type
``(Transitivity R)`` which is reducible to
``forall x,y:U, R x y -> forall z:U, R y z -> R x z``. As the variables ``x``, ``y`` and ``z``
appear strictly in the body of the type, they are implicit.

.. coqtop:: all

   Parameter X : Type.

   Definition Relation := X -> X -> Prop.

   Definition Transitivity (R:Relation) := forall x y:X, R x y -> forall z:X, R y z -> R x z.

   Parameters (R : Relation) (p : Transitivity R).

   Arguments p : default implicits.

   Print p.

   Print Implicit p.

   Parameters (a b c : X) (r1 : R a b) (r2 : R b c).

   Check (p r1 r2).


.. _renaming_implicit_arguments:

Renaming implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: (continued)  Renaming implicit arguments

   .. coqtop:: all

      Arguments p [s t] _ [u] _: rename.

      Check (p r1 (u:=c)).

      Check (p (s:=a) (t:=b) r1 (u:=c) r2).

      Fail Arguments p [s t] _ [w] _ : assert.

.. _binding_to_scope:

Binding arguments to a scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The following command declares that the first two arguments of :g:`plus_fct`
   are in the :token:`scope` delimited by the key ``F`` (``Rfun_scope``) and the third
   argument is in the scope delimited by the key ``R`` (``R_scope``).

      .. coqdoc::

         Arguments plus_fct (f1 f2)%F x%R.

   When interpreting a term, if some of the arguments of :token:`smart_global` are built
   from a notation, then this notation is interpreted in the scope stack
   extended by the scope (if any) that is bound to this argument. The effect of
   the scope is limited to the argument itself. It does not propagate to
   subterms but the subterms that, after interpretation of the notation,
   turn to be themselves arguments of a global reference are interpreted
   accordingly to the argument scopes bound to the global reference.

.. note::

   In notations, the subterms matching the identifiers of the
   notations are interpreted in the scope in which the identifiers
   occurred at the time of the declaration of the notation. Here is an
   example:

   .. coqtop:: all

      Parameter g : bool -> bool.
      Declare Scope mybool_scope.

      Notation "@@" := true (only parsing) : bool_scope.
      Notation "@@" := false (only parsing): mybool_scope.

      Bind Scope bool_scope with bool.
      Notation "# x #" := (g x) (at level 40).
      Check # @@ #.
      Arguments g _%mybool_scope.
      Check # @@ #.
      Delimit Scope mybool_scope with mybool.
      Check # @@%mybool #.

.. _Args_effect_on_unfolding:

Effects of :cmd:`Arguments` on unfolding
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

+ `simpl never` indicates that a constant should never be unfolded by :tacn:`cbn`,
  :tacn:`simpl` or :tacn:`hnf`:

  .. example::

     .. coqtop:: all

        Arguments minus n m : simpl never.

  After that command an expression like :g:`(minus (S x) y)` is left
  untouched by the tactics :tacn:`cbn` and :tacn:`simpl`.

+ A constant can be marked to be unfolded only if it's applied to at least
  the arguments appearing before the `/` in a :cmd:`Arguments` command.

  .. example::

     .. coqtop:: all

        Definition fcomp A B C f (g : A -> B) (x : A) : C := f (g x).
        Arguments fcomp {A B C} f g x /.
        Notation "f \o g" := (fcomp f g) (at level 50).

  After that command the expression :g:`(f \o g)` is left untouched by
  :tacn:`simpl` while :g:`((f \o g) t)` is reduced to :g:`(f (g t))`.
  The same mechanism can be used to make a constant volatile, i.e.
  always unfolded.

  .. example::

     .. coqtop:: all

        Definition volatile := fun x : nat => x.
        Arguments volatile / x.

+ A constant can be marked to be unfolded only if an entire set of
  arguments evaluates to a constructor. The ``!`` symbol can be used to mark
  such arguments.

  .. example::

     .. coqtop:: all

        Arguments minus !n !m.

  After that command, the expression :g:`(minus (S x) y)` is left untouched
  by :tacn:`simpl`, while :g:`(minus (S x) (S y))` is reduced to :g:`(minus x y)`.

+ `simpl nomatch` indicates that a constant should not be unfolded if it would expose
  a `match` construct in the head position.  This affects the :tacn:`cbn`,
  :tacn:`simpl` and :tacn:`hnf` tactics.

  .. example::

     .. coqtop:: all

        Arguments minus n m : simpl nomatch.

  In this case, :g:`(minus (S (S x)) (S y))` is simplified to :g:`(minus (S x) y)`
  even if an extra simplification is possible.

  In detail: the tactic :tacn:`simpl` first applies :math:`\beta`:math:`\iota`-reduction. Then, it
  expands transparent constants and tries to reduce further using :math:`\beta`:math:`\iota`-reduction.
  But, when no :math:`\iota` rule is applied after unfolding then
  :math:`\delta`-reductions are not applied. For instance trying to use :tacn:`simpl` on
  :g:`(plus n O) = n` changes nothing.


.. _bidirectionality_hints:

Bidirectionality hints
~~~~~~~~~~~~~~~~~~~~~~

When type-checking an application, Coq normally does not use information from
the context to infer the types of the arguments. It only checks after the fact
that the type inferred for the application is coherent with the expected type.
Bidirectionality hints make it possible to specify that after type-checking the
first arguments of an application, typing information should be propagated from
the context to help inferring the types of the remaining arguments.

.. todo the following text is a start on better wording but not quite complete.
   See https://github.com/coq/coq/pull/11718#discussion_r410219992

  ..
  Two common methods to determine the type of a construct are:

  * *type checking*, which is verifying that a construct matches a known type, and
  * *type inference*, with is inferring the type of a construct by analyzing the construct.

  Methods that combine these approaches are known as *bidirectional typing*.
  Coq normally uses only the first approach to infer the types of arguments,
  then later verifies that the inferred type is consistent with the expected type.
  *Bidirectionality hints* specify to use both methods: after type checking the
  first arguments of an application (appearing before the `&` in :cmd:`Arguments`),
  typing information from them is propagated to the remaining arguments to help infer their types.

An :cmd:`Arguments` command containing :n:`@arg_specs__1 & @arg_specs__2`
provides bidirectionality hints.
It tells the typechecking algorithm, when type checking
applications of :n:`@qualid`, to first type check the arguments in
:n:`@arg_specs__1` and then propagate information from the typing context to
type check the remaining arguments (in :n:`@arg_specs__2`).

.. example:: Bidirectionality hints

   In a context where a coercion was declared from ``bool`` to ``nat``:

   .. coqtop:: in reset

      Definition b2n (b : bool) := if b then 1 else 0.
      Coercion b2n : bool >-> nat.

   Coq cannot automatically coerce existential statements over ``bool`` to
   statements over ``nat``, because the need for inserting a coercion is known
   only from the expected type of a subterm:

   .. coqtop:: all

      Fail Check (ex_intro _ true _ : exists n : nat, n > 0).

   However, a suitable bidirectionality hint makes the example work:

   .. coqtop:: all

      Arguments ex_intro _ _ & _ _.
      Check (ex_intro _ true _ : exists n : nat, n > 0).

Coq will attempt to produce a term which uses the arguments you
provided, but in some cases involving Program mode the arguments after
the bidirectionality starts may be replaced by convertible but
syntactically different terms.
