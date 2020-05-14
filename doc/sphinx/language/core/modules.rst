.. _themodulesystem:

The Module System
=================

The module system extends the Calculus of Inductive Constructions
providing a convenient way to structure large developments as well as
a means of massive abstraction.


Modules and module types
----------------------------

**Access path.** An access path is denoted by :math:`p` and can be
either a module variable :math:`X` or, if :math:`p′` is an access path
and :math:`id` an identifier, then :math:`p′.id` is an access path.


**Structure element.** A structure element is denoted by :math:`e` and
is either a definition of a constant, an assumption, a definition of
an inductive, a definition of a module, an alias of a module or a module
type abbreviation.


**Structure expression.** A structure expression is denoted by :math:`S` and can be:

+ an access path :math:`p`
+ a plain structure :math:`\Struct~e ; … ; e~\End`
+ a functor :math:`\Functor(X:S)~S′`, where :math:`X` is a module variable, :math:`S` and :math:`S′` are
  structure expressions
+ an application :math:`S~p`, where :math:`S` is a structure expression and :math:`p` an
  access path
+ a refined structure :math:`S~\with~p := p`′ or :math:`S~\with~p := t:T` where :math:`S` is a
  structure expression, :math:`p` and :math:`p′` are access paths, :math:`t` is a term and :math:`T` is
  the type of :math:`t`.

**Module definition.** A module definition is written :math:`\Mod{X}{S}{S'}`
and consists of a module variable :math:`X`, a module type
:math:`S` which can be any structure expression and optionally a
module implementation :math:`S′` which can be any structure expression
except a refined structure.


**Module alias.** A module alias is written :math:`\ModA{X}{p}`
and consists of a module variable :math:`X` and a module path
:math:`p`.

**Module type abbreviation.**
A module type abbreviation is written :math:`\ModType{Y}{S}`,
where :math:`Y` is an identifier and :math:`S` is any structure
expression .

.. extracted from Gallina extensions chapter

Using modules
-------------

The module system provides a way of packaging related elements
together, as well as a means of massive abstraction.


.. cmd:: Module {? {| Import | Export } } @ident {* @module_binder } {? @of_module_type } {? := {+<+ @module_expr_inl } }

   .. insertprodn module_binder module_expr_inl

   .. prodn::
      module_binder ::= ( {? {| Import | Export } } {+ @ident } : @module_type_inl )
      module_type_inl ::= ! @module_type
      | @module_type {? @functor_app_annot }
      functor_app_annot ::= [ inline at level @num ]
      | [ no inline ]
      module_type ::= @qualid
      | ( @module_type )
      | @module_type @module_expr_atom
      | @module_type with @with_declaration
      with_declaration ::= Definition @qualid {? @univ_decl } := @term
      | Module @qualid := @qualid
      module_expr_atom ::= @qualid
      | ( {+ @module_expr_atom } )
      of_module_type ::= : @module_type_inl
      | {* <: @module_type_inl }
      module_expr_inl ::= ! {+ @module_expr_atom }
      | {+ @module_expr_atom } {? @functor_app_annot }

   Defines a module named :token:`ident`.  See the examples :ref:`here<module_examples>`.

   The :n:`Import` and :n:`Export` flags specify whether the module should be automatically
   imported or exported.

   Specifying :n:`{* @module_binder }` starts a functor with
   parameters given by the :n:`@module_binder`\s.  (A *functor* is a function
   from modules to modules.)

   :n:`@of_module_type` specifies the module type.  :n:`{+ <: @module_type_inl }`
   starts a module that satisfies each :n:`@module_type_inl`.

   .. todo: would like to find a better term than "interactive", not very descriptive

   :n:`:= {+<+ @module_expr_inl }` specifies the body of a module or functor
   definition.  If it's not specified, then the module is defined *interactively*,
   meaning that the module is defined as a series of commands terminated with :cmd:`End`
   instead of in a single :cmd:`Module` command.
   Interactively defining the :n:`@module_expr_inl`\s in a series of
   :cmd:`Include` commands is equivalent to giving them all in a single
   non-interactive :cmd:`Module` command.

   The ! prefix indicates that any assumption command (such as :cmd:`Axiom`) with an :n:`Inline` clause
   in the type of the functor arguments will be ignored.

   .. todo: What is an Inline directive?  sb command but still unclear.  Maybe referring to the
      "inline" in functor_app_annot?  or assumption_token Inline assum_list?

.. cmd:: Module Type @ident {* @module_binder } {* <: @module_type_inl } {? := {+<+ @module_type_inl } }

   Defines a module type named :n:`@ident`.  See the example :ref:`here<example_def_simple_module_type>`.

   Specifying :n:`{* @module_binder }` starts a functor type with
   parameters given by the :n:`@module_binder`\s.

   :n:`:= {+<+ @module_type_inl }` specifies the body of a module or functor type
   definition.  If it's not specified, then the module type is defined *interactively*,
   meaning that the module type is defined as a series of commands terminated with :cmd:`End`
   instead of in a single :cmd:`Module Type` command.
   Interactively defining the :n:`@module_type_inl`\s in a series of
   :cmd:`Include` commands is equivalent to giving them all in a single
   non-interactive :cmd:`Module Type` command.

.. _terminating_module:

**Terminating an interactive module or module type definition**

Interactive modules are terminated with the :cmd:`End` command, which
is also used to terminate :ref:`Sections<section-mechanism>`.
:n:`End @ident` closes the interactive module or module type :token:`ident`.
If the module type was given, the command verifies that the content of the module
matches the module type.  If the module is not a
functor, its components (constants, inductive types, submodules etc.)
are now available through the dot notation.

.. exn:: No such label @ident.
    :undocumented:

.. exn:: Signature components for label @ident do not match.
    :undocumented:

.. exn:: The field @ident is missing in @qualid.
   :undocumented:

.. |br| raw:: html

    <br>

.. note::

  #. Interactive modules and module types can be nested.
  #. Interactive modules and module types can't be defined inside of :ref:`sections<section-mechanism>`.
     Sections can be defined inside of interactive modules and module types.
  #. Hints and notations (:cmd:`Hint` and :cmd:`Notation` commands) can also appear inside interactive
     modules and module types. Note that with module definitions like:

     :n:`Module @ident__1 : @module_type := @ident__2.`

     or

     :n:`Module @ident__1 : @module_type.` |br|
     :n:`Include @ident__2.` |br|
     :n:`End @ident__1.`

     hints and the like valid for :n:`@ident__1` are the ones defined in :n:`@module_type`
     rather then those defined in :n:`@ident__2` (or the module body).
  #. Within an interactive module type definition, the :cmd:`Parameter` command declares a
     constant instead of definining a new axiom (which it does when not in a module type definition).
  #. Assumptions such as :cmd:`Axiom` that include the :n:`Inline` clause will be automatically
     expanded when the functor is applied, except when the function application is prefixed by ``!``.

.. cmd:: Include @module_type_inl {* <+ @module_expr_inl }

   Includes the content of module(s) in the current
   interactive module. Here :n:`@module_type_inl` can be a module expression or a module
   type expression. If it is a high-order module or module type
   expression then the system tries to instantiate :n:`@module_type_inl` with the current
   interactive module.

   Including multiple modules is a single :cmd:`Include` is equivalent to including each module
   in a separate :cmd:`Include` command.

.. cmd:: Include Type {+<+ @module_type_inl }

   .. deprecated:: 8.3

      Use :cmd:`Include` instead.

.. cmd:: Declare Module {? {| Import | Export } } @ident {* @module_binder } : @module_type_inl

   Declares a module :token:`ident` of type :token:`module_type_inl`.

   If :n:`@module_binder`\s are specified, declares a functor with parameters given by the list of
   :token:`module_binder`\s.

.. cmd:: Import {+ @filtered_import }

   .. insertprodn filtered_import filtered_import

   .. prodn::
      filtered_import ::= @qualid {? ( {+, @qualid {? ( .. ) } } ) }

   If :token:`qualid` denotes a valid basic module (i.e. its module type is a
   signature), makes its components available by their short names.

   .. example::

      .. coqtop:: reset in

         Module Mod.
         Definition T:=nat.
         Check T.
         End Mod.
         Check Mod.T.

      .. coqtop:: all

         Fail Check T.
         Import Mod.
         Check T.

   Some features defined in modules are activated only when a module is
   imported. This is for instance the case of notations (see :ref:`Notations`).

   Declarations made with the :attr:`local` attribute are never imported by the :cmd:`Import`
   command. Such declarations are only accessible through their fully
   qualified name.

   .. example::

      .. coqtop:: in

         Module A.
         Module B.
         Local Definition T := nat.
         End B.
         End A.
         Import A.

      .. coqtop:: all fail

         Check B.T.

   Appending a module name with a parenthesized list of names will
   make only those names available with short names, not other names
   defined in the module nor will it activate other features.

   The names to import may be constants, inductive types and
   constructors, and notation aliases (for instance, Ltac definitions
   cannot be selectively imported). If they are from an inner module
   to the one being imported, they must be prefixed by the inner path.

   The name of an inductive type may also be followed by ``(..)`` to
   import it, its constructors and its eliminators if they exist. For
   this purpose "eliminator" means a constant in the same module whose
   name is the inductive type's name suffixed by one of ``_sind``,
   ``_ind``, ``_rec`` or ``_rect``.

   .. example::

      .. coqtop:: reset in

         Module A.
         Module B.
         Inductive T := C.
         Definition U := nat.
         End B.
         Definition Z := Prop.
         End A.
         Import A(B.T(..), Z).

      .. coqtop:: all

         Check B.T.
         Check B.C.
         Check Z.
         Fail Check B.U.
         Check A.B.U.

.. cmd:: Export {+ @filtered_import }
   :name: Export

   Similar to :cmd:`Import`, except that when the module containing this command
   is imported, the :n:`{+ @qualid }` are imported as well.

   The selective import syntax also works with Export.

   .. exn:: @qualid is not a module.
      :undocumented:

   .. warn:: Trying to mask the absolute name @qualid!
      :undocumented:

.. cmd:: Print Module @qualid

   Prints the module type and (optionally) the body of the module :n:`@qualid`.

.. cmd:: Print Module Type @qualid

   Prints the module type corresponding to :n:`@qualid`.

.. flag:: Short Module Printing

   This flag (off by default) disables the printing of the types of fields,
   leaving only their names, for the commands :cmd:`Print Module` and
   :cmd:`Print Module Type`.

.. _module_examples:

Examples
~~~~~~~~

.. example:: Defining a simple module interactively

    .. coqtop:: in

       Module M.
       Definition T := nat.
       Definition x := 0.

    .. coqtop:: all

       Definition y : bool.
       exact true.

    .. coqtop:: in

       Defined.
       End M.

Inside a module one can define constants, prove theorems and do anything
else that can be done in the toplevel. Components of a closed
module can be accessed using the dot notation:

.. coqtop:: all

   Print M.x.

.. _example_def_simple_module_type:

.. example:: Defining a simple module type interactively

   .. coqtop:: in

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

.. _example_filter_module:

.. example:: Creating a new module that omits some items from an existing module

   Since :n:`SIG`, the type of the new module :n:`N`, doesn't define :n:`y` or
   give the body of :n:`x`, which are not included in :n:`N`.

   .. coqtop:: all

      Module N : SIG with Definition T := nat := M.
      Print N.T.
      Print N.x.
      Fail Print N.y.

   .. reset to remove N (undo in last coqtop block doesn't seem to do that), invisibly redefine M, SIG
   .. coqtop:: none reset

      Module M.
      Definition T := nat.
      Definition x := 0.
      Definition y : bool.
      exact true.
      Defined.
      End M.

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

The definition of :g:`N` using the module type expression :g:`SIG` with
:g:`Definition T := nat` is equivalent to the following one:

.. coqtop:: in

   Module Type SIG'.
   Definition T : Set := nat.
   Parameter x : T.
   End SIG'.

   Module N : SIG' := M.

If we just want to be sure that our implementation satisfies a
given module type without restricting the interface, we can use a
transparent constraint

.. coqtop:: in

   Module P <: SIG := M.

.. coqtop:: all

   Print P.y.

.. example:: Creating a functor (a module with parameters)

   .. coqtop:: in

      Module Two (X Y: SIG).
      Definition T := (X.T * Y.T)%type.
      Definition x := (X.x, Y.x).
      End Two.

   and apply it to our modules and do some computations:

   .. coqtop:: in


      Module Q := Two M N.

   .. coqtop:: all

      Eval compute in (fst Q.x + snd Q.x).

.. example:: A module type with two sub-modules, sharing some fields

   .. coqtop:: in

      Module Type SIG2.
        Declare Module M1 : SIG.
        Module M2 <: SIG.
          Definition T := M1.T.
          Parameter x : T.
        End M2.
      End SIG2.

   .. coqtop:: in

      Module Mod <: SIG2.
        Module M1.
          Definition T := nat.
          Definition x := 1.
        End M1.
      Module M2 := M.
      End Mod.

Notice that ``M`` is a correct body for the component ``M2`` since its ``T``
component is ``nat`` as specified for ``M1.T``.

Typing Modules
------------------

In order to introduce the typing system we first slightly extend the syntactic
class of terms and environments given in section :ref:`The-terms`. The
environments, apart from definitions of constants and inductive types now also
hold any other structure elements. Terms, apart from variables, constants and
complex terms, include also access paths.

We also need additional typing judgments:


+ :math:`\WFT{E}{S}`, denoting that a structure :math:`S` is well-formed,
+ :math:`\WTM{E}{p}{S}`, denoting that the module pointed by :math:`p` has type :math:`S` in
  environment :math:`E`.
+ :math:`\WEV{E}{S}{\ovl{S}}`, denoting that a structure :math:`S` is evaluated to a
  structure :math:`S` in weak head normal form.
+ :math:`\WS{E}{S_1}{S_2}` , denoting that a structure :math:`S_1` is a subtype of a
  structure :math:`S_2`.
+ :math:`\WS{E}{e_1}{e_2}` , denoting that a structure element e_1 is more
  precise than a structure element e_2.

The rules for forming structures are the following:

.. inference:: WF-STR

   \WF{E;E′}{}
   ------------------------
   \WFT{E}{ \Struct~E′ ~\End}

.. inference:: WF-FUN

   \WFT{E; \ModS{X}{S}}{ \ovl{S′} }
   --------------------------
   \WFT{E}{ \Functor(X:S)~S′}


Evaluation of structures to weak head normal form:

.. inference:: WEVAL-APP

   \begin{array}{c}
   \WEV{E}{S}{\Functor(X:S_1 )~S_2}~~~~~\WEV{E}{S_1}{\ovl{S_1}} \\
   \WTM{E}{p}{S_3}~~~~~ \WS{E}{S_3}{\ovl{S_1}}
   \end{array}
   --------------------------
   \WEV{E}{S~p}{S_2 \{p/X,t_1 /p_1 .c_1 ,…,t_n /p_n.c_n \}}


In the last rule, :math:`\{t_1 /p_1 .c_1 ,…,t_n /p_n .c_n \}` is the resulting
substitution from the inlining mechanism. We substitute in :math:`S` the
inlined fields :math:`p_i .c_i` from :math:`\ModS{X}{S_1 }` by the corresponding delta-
reduced term :math:`t_i` in :math:`p`.

.. inference:: WEVAL-WITH-MOD

   \begin{array}{c}
   E[] ⊢ S \lra \Struct~e_1 ;…;e_i ; \ModS{X}{S_1 };e_{i+2} ;… ;e_n ~\End \\
   E;e_1 ;…;e_i [] ⊢ S_1 \lra \ovl{S_1} ~~~~~~
   E[] ⊢ p : S_2 \\
   E;e_1 ;…;e_i [] ⊢ S_2 <: \ovl{S_1}
   \end{array}
   ----------------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~x := p}{}\\
   \Struct~e_1 ;…;e_i ; \ModA{X}{p};e_{i+2} \{p/X\} ;…;e_n \{p/X\} ~\End
   \end{array}

.. inference:: WEVAL-WITH-MOD-REC

   \begin{array}{c}
   \WEV{E}{S}{\Struct~e_1 ;…;e_i ; \ModS{X_1}{S_1 };e_{i+2} ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{S_1~\with~p := p_1}{\ovl{S_2}}
   \end{array}
   --------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~X_1.p := p_1}{} \\
   \Struct~e_1 ;…;e_i ; \ModS{X}{\ovl{S_2}};e_{i+2} \{p_1 /X_1.p\} ;…;e_n \{p_1 /X_1.p\} ~\End
   \end{array}

.. inference:: WEVAL-WITH-DEF

   \begin{array}{c}
   \WEV{E}{S}{\Struct~e_1 ;…;e_i ;\Assum{}{c}{T_1};e_{i+2} ;… ;e_n ~\End} \\
   \WS{E;e_1 ;…;e_i }{Def()(c:=t:T)}{\Assum{}{c}{T_1}}
   \end{array}
   --------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~c := t:T}{} \\
   \Struct~e_1 ;…;e_i ;Def()(c:=t:T);e_{i+2} ;… ;e_n ~\End
   \end{array}

.. inference:: WEVAL-WITH-DEF-REC

   \begin{array}{c}
   \WEV{E}{S}{\Struct~e_1 ;…;e_i ; \ModS{X_1 }{S_1 };e_{i+2} ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{S_1~\with~p := p_1}{\ovl{S_2}}
   \end{array}
   --------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~X_1.p := t:T}{} \\
   \Struct~e_1 ;…;e_i ; \ModS{X}{\ovl{S_2} };e_{i+2} ;… ;e_n ~\End
   \end{array}

.. inference:: WEVAL-PATH-MOD1

   \begin{array}{c}
   \WEV{E}{p}{\Struct~e_1 ;…;e_i ; \Mod{X}{S}{S_1};e_{i+2} ;… ;e_n End} \\
   \WEV{E;e_1 ;…;e_i }{S}{\ovl{S}}
   \end{array}
   --------------------------
   E[] ⊢ p.X \lra \ovl{S}

.. inference:: WEVAL-PATH-MOD2

   \WF{E}{}
   \Mod{X}{S}{S_1}∈ E
   \WEV{E}{S}{\ovl{S}}
   --------------------------
   \WEV{E}{X}{\ovl{S}}

.. inference:: WEVAL-PATH-ALIAS1

   \begin{array}{c}
   \WEV{E}{p}{~\Struct~e_1 ;…;e_i ; \ModA{X}{p_1};e_{i+2}  ;… ;e_n End} \\
   \WEV{E;e_1 ;…;e_i }{p_1}{\ovl{S}}
   \end{array}
   --------------------------
   \WEV{E}{p.X}{\ovl{S}}

.. inference:: WEVAL-PATH-ALIAS2

   \WF{E}{}
   \ModA{X}{p_1 }∈ E
   \WEV{E}{p_1}{\ovl{S}}
   --------------------------
   \WEV{E}{X}{\ovl{S}}

.. inference:: WEVAL-PATH-TYPE1

   \begin{array}{c}
   \WEV{E}{p}{~\Struct~e_1 ;…;e_i ; \ModType{Y}{S};e_{i+2} ;… ;e_n End} \\
   \WEV{E;e_1 ;…;e_i }{S}{\ovl{S}}
   \end{array}
   --------------------------
   \WEV{E}{p.Y}{\ovl{S}}

.. inference:: WEVAL-PATH-TYPE2

   \WF{E}{}
   \ModType{Y}{S}∈ E
   \WEV{E}{S}{\ovl{S}}
   --------------------------
   \WEV{E}{Y}{\ovl{S}}


Rules for typing module:

.. inference:: MT-EVAL

   \WEV{E}{p}{\ovl{S}}
   --------------------------
   E[] ⊢ p : \ovl{S}

.. inference:: MT-STR

   E[] ⊢ p : S
   --------------------------
   E[] ⊢ p : S/p


The last rule, called strengthening is used to make all module fields
manifestly equal to themselves. The notation :math:`S/p` has the following
meaning:


+ if :math:`S\lra~\Struct~e_1 ;…;e_n ~\End` then :math:`S/p=~\Struct~e_1 /p;…;e_n /p ~\End`
  where :math:`e/p` is defined as follows (note that opaque definitions are processed
  as assumptions):

    + :math:`\Def{}{c}{t}{T}/p = \Def{}{c}{t}{T}`
    + :math:`\Assum{}{c}{U}/p = \Def{}{c}{p.c}{U}`
    + :math:`\ModS{X}{S}/p = \ModA{X}{p.X}`
    + :math:`\ModA{X}{p′}/p = \ModA{X}{p′}`
    + :math:`\Ind{}{Γ_P}{Γ_C}{Γ_I}/p = \Indp{}{Γ_P}{Γ_C}{Γ_I}{p}`
    + :math:`\Indpstr{}{Γ_P}{Γ_C}{Γ_I}{p'}{p} = \Indp{}{Γ_P}{Γ_C}{Γ_I}{p'}`

+ if :math:`S \lra \Functor(X:S′)~S″` then :math:`S/p=S`


The notation :math:`\Indp{}{Γ_P}{Γ_C}{Γ_I}{p}`
denotes an inductive definition that is definitionally equal to the
inductive definition in the module denoted by the path :math:`p`. All rules
which have :math:`\Ind{}{Γ_P}{Γ_C}{Γ_I}` as premises are also valid for
:math:`\Indp{}{Γ_P}{Γ_C}{Γ_I}{p}`. We give the formation rule for
:math:`\Indp{}{Γ_P}{Γ_C}{Γ_I}{p}`
below as well as the equality rules on inductive types and
constructors.

The module subtyping rules:

.. inference:: MSUB-STR

   \begin{array}{c}
   \WS{E;e_1 ;…;e_n }{e_{σ(i)}}{e'_i ~\for~ i=1..m} \\
   σ : \{1… m\} → \{1… n\} ~\injective
   \end{array}
   --------------------------
   \WS{E}{\Struct~e_1 ;…;e_n ~\End}{~\Struct~e'_1 ;…;e'_m ~\End}

.. inference:: MSUB-FUN

   \WS{E}{\ovl{S_1'}}{\ovl{S_1}}
   \WS{E; \ModS{X}{S_1'}}{\ovl{S_2}}{\ovl{S_2'}}
   --------------------------
   E[] ⊢ \Functor(X:S_1 ) S_2 <: \Functor(X:S_1') S_2'


Structure element subtyping rules:

.. inference:: ASSUM-ASSUM

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   --------------------------
   \WS{E}{\Assum{}{c}{T_1 }}{\Assum{}{c}{T_2 }}

.. inference:: DEF-ASSUM

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   --------------------------
   \WS{E}{\Def{}{c}{t}{T_1 }}{\Assum{}{c}{T_2 }}

.. inference:: ASSUM-DEF

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   E[] ⊢ c =_{βδιζη} t_2
   --------------------------
   \WS{E}{\Assum{}{c}{T_1 }}{\Def{}{c}{t_2 }{T_2 }}

.. inference:: DEF-DEF

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   E[] ⊢ t_1 =_{βδιζη} t_2
   --------------------------
   \WS{E}{\Def{}{c}{t_1 }{T_1 }}{\Def{}{c}{t_2 }{T_2 }}

.. inference:: IND-IND

   E[] ⊢ Γ_P =_{βδιζη} Γ_P'
   E[Γ_P ] ⊢ Γ_C =_{βδιζη} Γ_C'
   E[Γ_P ;Γ_C ] ⊢ Γ_I =_{βδιζη} Γ_I'
   --------------------------
   \WS{E}{\ind{Γ_P}{Γ_C}{Γ_I}}{\ind{Γ_P'}{Γ_C'}{Γ_I'}}

.. inference:: INDP-IND

   E[] ⊢ Γ_P =_{βδιζη} Γ_P'
   E[Γ_P ] ⊢ Γ_C =_{βδιζη} Γ_C'
   E[Γ_P ;Γ_C ] ⊢ Γ_I =_{βδιζη} Γ_I'
   --------------------------
   \WS{E}{\Indp{}{Γ_P}{Γ_C}{Γ_I}{p}}{\ind{Γ_P'}{Γ_C'}{Γ_I'}}

.. inference:: INDP-INDP

   \begin{array}{c}
   E[] ⊢ Γ_P =_{βδιζη} Γ_P'
   E[Γ_P ] ⊢ Γ_C =_{βδιζη} Γ_C' \\
   E[Γ_P ;Γ_C ] ⊢ Γ_I =_{βδιζη} Γ_I'
   E[] ⊢ p =_{βδιζη} p'
   \end{array}
   --------------------------
   \WS{E}{\Indp{}{Γ_P}{Γ_C}{Γ_I}{p}}{\Indp{}{Γ_P'}{Γ_C'}{Γ_I'}{p'}}

.. inference:: MOD-MOD

   \WS{E}{S_1}{S_2}
   --------------------------
   \WS{E}{\ModS{X}{S_1 }}{\ModS{X}{S_2 }}

.. inference:: ALIAS-MOD

   E[] ⊢ p : S_1
   \WS{E}{S_1}{S_2}
   --------------------------
   \WS{E}{\ModA{X}{p}}{\ModS{X}{S_2 }}

.. inference:: MOD-ALIAS

   E[] ⊢ p : S_2
   \WS{E}{S_1}{S_2}
   E[] ⊢ X =_{βδιζη} p
   --------------------------
   \WS{E}{\ModS{X}{S_1 }}{\ModA{X}{p}}

.. inference:: ALIAS-ALIAS

   E[] ⊢ p_1 =_{βδιζη} p_2
   --------------------------
   \WS{E}{\ModA{X}{p_1 }}{\ModA{X}{p_2 }}

.. inference:: MODTYPE-MODTYPE

   \WS{E}{S_1}{S_2}
   \WS{E}{S_2}{S_1}
   --------------------------
   \WS{E}{\ModType{Y}{S_1 }}{\ModType{Y}{S_2 }}


New environment formation rules


.. inference:: WF-MOD1

   \WF{E}{}
   \WFT{E}{S}
   --------------------------
   WF(E; \ModS{X}{S})[]

.. inference:: WF-MOD2

   \WS{E}{S_2}{S_1}
   \WF{E}{}
   \WFT{E}{S_1}
   \WFT{E}{S_2}
   --------------------------
   \WF{E; \Mod{X}{S_1}{S_2}}{}

.. inference:: WF-ALIAS

   \WF{E}{}
   E[] ⊢ p : S
   --------------------------
   \WF{E, \ModA{X}{p}}{}

.. inference:: WF-MODTYPE

   \WF{E}{}
   \WFT{E}{S}
   --------------------------
   \WF{E, \ModType{Y}{S}}{}

.. inference:: WF-IND

   \begin{array}{c}
   \WF{E;\ind{Γ_P}{Γ_C}{Γ_I}}{} \\
   E[] ⊢ p:~\Struct~e_1 ;…;e_n ;\ind{Γ_P'}{Γ_C'}{Γ_I'};… ~\End : \\
   E[] ⊢ \ind{Γ_P'}{Γ_C'}{Γ_I'} <: \ind{Γ_P}{Γ_C}{Γ_I}
   \end{array}
   --------------------------
   \WF{E; \Indp{}{Γ_P}{Γ_C}{Γ_I}{p} }{}


Component access rules


.. inference:: ACC-TYPE1

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\Assum{}{c}{T};… ~\End
   --------------------------
   E[Γ] ⊢ p.c : T

.. inference:: ACC-TYPE2

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\Def{}{c}{t}{T};… ~\End
   --------------------------
   E[Γ] ⊢ p.c : T

Notice that the following rule extends the delta rule defined in section :ref:`Conversion-rules`

.. inference:: ACC-DELTA

    E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\Def{}{c}{t}{U};… ~\End
    --------------------------
    E[Γ] ⊢ p.c \triangleright_δ t

In the rules below we assume
:math:`Γ_P` is :math:`[p_1 :P_1 ;…;p_r :P_r ]`,
:math:`Γ_I` is :math:`[I_1 :A_1 ;…;I_k :A_k ]`,
and :math:`Γ_C` is :math:`[c_1 :C_1 ;…;c_n :C_n ]`.

.. inference:: ACC-IND1

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\ind{Γ_P}{Γ_C}{Γ_I};… ~\End
   --------------------------
   E[Γ] ⊢ p.I_j : (p_1 :P_1 )…(p_r :P_r )A_j

.. inference:: ACC-IND2

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\ind{Γ_P}{Γ_C}{Γ_I};… ~\End
   --------------------------
   E[Γ] ⊢ p.c_m : (p_1 :P_1 )…(p_r :P_r )C_m I_j (I_j~p_1 …p_r )_{j=1… k}

.. inference:: ACC-INDP1

   E[] ⊢ p :~\Struct~e_1 ;…;e_i ; \Indp{}{Γ_P}{Γ_C}{Γ_I}{p'} ;… ~\End
   --------------------------
   E[] ⊢ p.I_i \triangleright_δ p'.I_i

.. inference:: ACC-INDP2

   E[] ⊢ p :~\Struct~e_1 ;…;e_i ; \Indp{}{Γ_P}{Γ_C}{Γ_I}{p'} ;… ~\End
   --------------------------
   E[] ⊢ p.c_i \triangleright_δ p'.c_i

.. extracted from Gallina extensions chapter

Libraries and qualified names
---------------------------------

.. _names-of-libraries:

Names of libraries
~~~~~~~~~~~~~~~~~~

The theories developed in |Coq| are stored in *library files* which are
hierarchically classified into *libraries* and *sublibraries*. To
express this hierarchy, library names are represented by qualified
identifiers qualid, i.e. as list of identifiers separated by dots (see
:ref:`qualified-names`). For instance, the library file ``Mult`` of the standard
|Coq| library ``Arith`` is named ``Coq.Arith.Mult``. The identifier that starts
the name of a library is called a *library root*. All library files of
the standard library of |Coq| have the reserved root |Coq| but library
filenames based on other roots can be obtained by using |Coq| commands
(coqc, coqtop, coqdep, …) options ``-Q`` or ``-R`` (see :ref:`command-line-options`).
Also, when an interactive |Coq| session starts, a library of root ``Top`` is
started, unless option ``-top`` or ``-notop`` is set (see :ref:`command-line-options`).

.. _qualified-names:

Qualified identifiers
---------------------

.. insertprodn qualid field_ident

.. prodn::
   qualid ::= @ident {* @field_ident }
   field_ident ::= .@ident

Library files are modules which possibly contain submodules which
eventually contain constructions (axioms, parameters, definitions,
lemmas, theorems, remarks or facts). The *absolute name*, or *full
name*, of a construction in some library file is a qualified
identifier starting with the logical name of the library file,
followed by the sequence of submodules names encapsulating the
construction and ended by the proper name of the construction.
Typically, the absolute name ``Coq.Init.Logic.eq`` denotes Leibniz’
equality defined in the module Logic in the sublibrary ``Init`` of the
standard library of |Coq|.

The proper name that ends the name of a construction is the short name
(or sometimes base name) of the construction (for instance, the short
name of ``Coq.Init.Logic.eq`` is ``eq``). Any partial suffix of the absolute
name is a *partially qualified name* (e.g. ``Logic.eq`` is a partially
qualified name for ``Coq.Init.Logic.eq``). Especially, the short name of a
construction is its shortest partially qualified name.

|Coq| does not accept two constructions (definition, theorem, …) with
the same absolute name but different constructions can have the same
short name (or even same partially qualified names as soon as the full
names are different).

Notice that the notion of absolute, partially qualified and short
names also applies to library filenames.

**Visibility**

|Coq| maintains a table called the name table which maps partially qualified
names of constructions to absolute names. This table is updated by the
commands :cmd:`Require`, :cmd:`Import` and :cmd:`Export` and
also each time a new declaration is added to the context. An absolute
name is called visible from a given short or partially qualified name
when this latter name is enough to denote it. This means that the
short or partially qualified name is mapped to the absolute name in
|Coq| name table. Definitions with the :attr:`local` attribute are only accessible with
their fully qualified name (see :ref:`gallina-definitions`).

It may happen that a visible name is hidden by the short name or a
qualified name of another construction. In this case, the name that
has been hidden must be referred to using one more level of
qualification. To ensure that a construction always remains
accessible, absolute names can never be hidden.

.. example::

    .. coqtop:: all

       Check 0.

       Definition nat := bool.

       Check 0.

       Check Datatypes.nat.

       Locate nat.

.. seealso:: Commands :cmd:`Locate`.

.. _libraries-and-filesystem:

Libraries and filesystem
~~~~~~~~~~~~~~~~~~~~~~~~

.. note:: The questions described here have been subject to redesign in |Coq| 8.5.
   Former versions of |Coq| use the same terminology to describe slightly different things.

Compiled files (``.vo`` and ``.vio``) store sub-libraries. In order to refer
to them inside |Coq|, a translation from file-system names to |Coq| names
is needed. In this translation, names in the file system are called
*physical* paths while |Coq| names are contrastingly called *logical*
names.

A logical prefix Lib can be associated with a physical path using
the command line option ``-Q`` `path` ``Lib``. All subfolders of path are
recursively associated to the logical path ``Lib`` extended with the
corresponding suffix coming from the physical path. For instance, the
folder ``path/fOO/Bar`` maps to ``Lib.fOO.Bar``. Subdirectories corresponding
to invalid |Coq| identifiers are skipped, and, by convention,
subdirectories named ``CVS`` or ``_darcs`` are skipped too.

Thanks to this mechanism, ``.vo`` files are made available through the
logical name of the folder they are in, extended with their own
basename. For example, the name associated to the file
``path/fOO/Bar/File.vo`` is ``Lib.fOO.Bar.File``. The same caveat applies for
invalid identifiers. When compiling a source file, the ``.vo`` file stores
its logical name, so that an error is issued if it is loaded with the
wrong loadpath afterwards.

Some folders have a special status and are automatically put in the
path. |Coq| commands associate automatically a logical path to files in
the repository trees rooted at the directory from where the command is
launched, ``coqlib/user-contrib/``, the directories listed in the
``$COQPATH``, ``${XDG_DATA_HOME}/coq/`` and ``${XDG_DATA_DIRS}/coq/``
environment variables (see `XDG base directory specification
<http://standards.freedesktop.org/basedir-spec/basedir-spec-latest.html>`_)
with the same physical-to-logical translation and with an empty logical prefix.

The command line option ``-R`` is a variant of ``-Q`` which has the strictly
same behavior regarding loadpaths, but which also makes the
corresponding ``.vo`` files available through their short names in a way
similar to the :cmd:`Import` command. For instance, ``-R path Lib``
associates to the file ``/path/fOO/Bar/File.vo`` the logical name
``Lib.fOO.Bar.File``, but allows this file to be accessed through the
short names ``fOO.Bar.File,Bar.File`` and ``File``. If several files with
identical base name are present in different subdirectories of a
recursive loadpath, which of these files is found first may be system-
dependent and explicit qualification is recommended. The ``From`` argument
of the ``Require`` command can be used to bypass the implicit shortening
by providing an absolute root to the required file (see :ref:`compiled-files`).

There also exists another independent loadpath mechanism attached to
OCaml object files (``.cmo`` or ``.cmxs``) rather than |Coq| object
files as described above. The OCaml loadpath is managed using
the option ``-I`` `path` (in the OCaml world, there is neither a
notion of logical name prefix nor a way to access files in
subdirectories of path). See the command :cmd:`Declare ML Module` in
:ref:`compiled-files` to understand the need of the OCaml loadpath.

See :ref:`command-line-options` for a more general view over the |Coq| command
line options.
