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
