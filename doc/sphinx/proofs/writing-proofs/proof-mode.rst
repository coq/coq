.. _proofhandling:

----------
Proof mode
----------

:gdef:`Proof mode <proof mode>` is used to prove theorems.
Rocq enters proof mode when you begin a proof,
such as with the :cmd:`Theorem` command.  It exits proof mode when
you complete a proof, such as with the :cmd:`Qed` command.  Tactics,
which are available only in proof mode, incrementally transform incomplete
proofs to eventually generate a complete proof.

When you run Rocq interactively, such as through RocqIDE, Proof General or
`rocq repl`, Rocq shows the current proof state (the incomplete proof) as you
enter tactics.  This information isn't shown when you run Rocq in batch
mode with `rocq compile`.

Proof State
-----------

The :gdef:`proof state` consists of one or more unproven goals.
Each goal has a :gdef:`conclusion` (the statement that is to be proven)
and a :gdef:`local context`, which contains named :term:`hypotheses <hypothesis>`
(which are propositions), variables and local definitions that can be used in
proving the conclusion.  The proof may also use *constants* from the :term:`global environment`
such as definitions and proven theorems.

.. _conclusion_meaning_2:

(Note that *conclusion* is also used to refer to the last part of an implication.
For example, in `A -> B -> C`, `A` and `B` are :term:`premises <premise>` and `C`
is the conclusion.)

The term ":gdef:`goal`" may refer to an entire goal or to the conclusion
of a goal, depending on the context.

The conclusion appears below a line and the local context appears above the line.
The conclusion is a type.  Each item in the local context begins with a name
and ends, after a colon, with an associated type.
:gdef:`Local definitions <context-local definition>`
are shown in the form `n := 0 : nat`, for example, in which `nat` is the
type of `0`.

The local context of a goal contains items specific to the goal as well
as section-local variables and hypotheses (see :ref:`gallina-assumptions`) defined
in the current :ref:`section <section-mechanism>`.  The latter are included in the
initial proof state.
Items in the local context are ordered; an item can only refer to items that appear
before it.  (A more mathematical description of the *local context* is
:ref:`here <Local-context>`.)

The :gdef:`global environment` has definitions and proven theorems that are global in scope.
(A more mathematical description of the *global environment* is :ref:`here <Global-environment>`.)

When you begin proving a theorem, the proof state shows
the statement of the theorem below the line and often nothing in the
local context:

.. rocqtop:: none

   Parameter P: nat -> Prop.

.. rocqtop:: out

   Goal forall n m: nat, n > m -> P 1 /\ P 2.

After applying the :tacn:`intros` :term:`tactic`, we see hypotheses above the line.
The names of variables (`n` and `m`) and hypotheses (`H`) appear before a colon, followed by
their type.  The type doesn't have to be a provable statement.
For example, `0 = 1` and `False` are both valid and useful types.

.. rocqtop:: all

   intros.

Some tactics, such as :tacn:`split`, create new goals, which may
be referred to as :gdef:`subgoals <subgoal>` for clarity.
Goals are numbered from 1 to N at each step of the proof to permit applying a
tactic to specific goals.  The local context is only shown for the first goal.

.. rocqtop:: all

   split.

:gdef:`"Variables" <variable>` may refer specifically to local context items introduced
from :n:`forall` variables for which the type of their type
is `Set` or `Type`. :gdef:`"Hypotheses" <hypothesis>` refers to items that are
:term:`propositions <proposition>`,
for which the type of their type is `Prop` or `SProp`,
but these terms are also used interchangeably.

.. rocqtop:: out

   let t_n := type of n in idtac "type of n :" t_n;
   let tt_n := type of t_n in idtac "type of" t_n ":" tt_n.
   let t_H := type of H in idtac "type of H :" t_H;
   let tt_H := type of t_H in idtac "type of" t_H ":" tt_H.

A proof script, consisting of the tactics that are applied to prove a
theorem, is often informally referred to as a "proof".
The real proof, whether complete or incomplete, is the associated term,
the :gdef:`proof term`, which users may occasionally want to examine.
(This is based on the
*Curry-Howard isomorphism* :cite:`How80,Bar81,Gir89,H89`, which is
a correspondence between between proofs and terms and between
:term:`propositions <proposition>` and types of λ-calculus.  The isomorphism
is also sometimes called the "propositions-as-types correspondence".)

The :cmd:`Show Proof` command displays the incomplete proof term
before you've completed the proof.  For example, here's the proof
term after using the :tacn:`split` tactic above:

.. rocqtop:: all

   Show Proof.

The incomplete parts, the goals, are represented by
:term:`existential variables <existential variable>`
with names that begin with `?Goal`.  (Note that some existential variables
are not goals.)  The :cmd:`Show Existentials` command shows each existential with
the hypotheses and conclusion for the associated goal.

.. rocqtop:: all

   Show Existentials.

Users can control which goals are displayed in the context by :term:`focusing <focus>`
goals.  Focusing lets the user (initially) pick a single goal to work on.  Focusing
operations can be nested.

Tactics such as :tacn:`eapply` create existential variables as placeholders for
undetermined variables that become :term:`shelved <shelved>` goals.
Shelved goals are not shown in the context by default, but they can be unshelved
to make them visible.  Other tactics may automatically resolve these goals
(whether shelved or not); the purpose of shelving is to hide goals that the
user usually doesn't need to think about.  See :ref:`existential-variables`
and :ref:`this example <automatic-evar-resolution>`.

Rocq's kernel verifies the correctness of proof terms when it exits
proof mode by checking that the proof term is :term:`well-typed` and
that its type is the same as the theorem statement.

After a proof is completed, :cmd:`Print` `<theorem_name>`
shows the proof term and its type.  The type appears after
the colon (`forall ...`), as for this theorem from Rocq's standard library:

.. rocqtop:: all

   Print proj1.

.. note::
   Many tactics accept :n:`@term`\s as arguments and frequently
   refer to them with wording such as "the type of :token:`term`".
   When :n:`@term` is the name of a theorem or lemma, this wording
   refers to the type of the proof term, which is what's given in the
   :cmd:`Theorem` statement.  When :n:`@term` is the name of a hypothesis,
   the wording refers to the type shown in the context for the hypothesis
   (i.e., after the colon).
   For terms that are more complex than just an :token:`ident`,
   you can use :cmd:`Check` :n:`@term` to display their type.

.. _proof-editing-mode:

Entering and exiting proof mode
-------------------------------

Rocq enters :term:`proof mode` when you begin a proof through
commands such as :cmd:`Theorem` or :cmd:`Goal`.  Rocq user interfaces
usually have a way to indicate that you're in proof mode.

:term:`Tactics <tactic>` are available only in proof mode (currently they give syntax
errors outside of proof mode).  Most :term:`commands <command>` can be used both in and out of
proof mode, but some commands only work in or outside of proof mode.

When the proof is completed, you can exit proof mode with commands such as
:cmd:`Qed`, :cmd:`Defined` and :cmd:`Save`.

.. cmd:: Goal @type

   Asserts an unnamed proposition.  This is intended for quick tests that
   a proposition is provable.  If the proof is eventually completed and
   validated, you can assign a name with the :cmd:`Save` or :cmd:`Defined`
   commands.  If no name is given, the name will be `Unnamed_thm` (or,
   if that name is already defined, a variant of that).

.. cmd:: Qed

   Passes a completed :term:`proof term` to Rocq's kernel
   to check that the proof term is :term:`well-typed` and
   to verify that its type matches the theorem statement.  If it's verified, the
   proof term is added to the global environment as an :term:`opaque` constant
   using the declared name from the original goal.

   It's very rare for a proof term to fail verification.  Generally this
   indicates a bug in a tactic you used or that you misused some
   unsafe tactics.

   .. exn:: Attempt to save an incomplete proof.
      :undocumented:

   .. exn:: No focused proof (No proof-editing in progress).

      You tried to use a proof mode command such as :cmd:`Qed` outside of proof
      mode.

   .. note::

      Sometimes an error occurs when building the proof term, because
      tactics do not enforce completely the term construction
      constraints.

      The user should also be aware of the fact that since the
      proof term is completely rechecked at this point, one may have to wait
      a while when the proof is large. In some exceptional cases one may
      even incur a memory overflow.

.. cmd:: Save @ident

   Similar to :cmd:`Qed`, except that the proof term is added to the global
   context with the name :token:`ident`, which
   overrides any name provided by the :cmd:`Theorem` command or
   its variants.

.. cmd:: Defined {? @ident }

   Similar to :cmd:`Qed` and :cmd:`Save`, except the proof is made
   :term:`transparent`, which means
   that its content can be explicitly used for type checking and that it can be
   unfolded in conversion tactics (see :ref:`applyingconversionrules`,
   :cmd:`Opaque`, :cmd:`Transparent`).  If :token:`ident` is specified,
   the proof is defined with the given name, which overrides any name
   provided by the :cmd:`Theorem` command or its variants.

.. cmd:: Admitted

   This command is available in proof mode to give up
   the current proof and declare the initial goal as an axiom.

.. cmd:: Abort {? All }

   Aborts the current proof.  If the current proof is a nested proof, the previous
   proof becomes current.  If :n:`All` is given, all nested proofs are aborted.
   See :flag:`Nested Proofs Allowed`.

   :n:`All`
     Aborts all current proofs.

.. cmd:: Proof @term
   :name: Proof `term`

   This command applies in proof mode. It is equivalent to
   :n:`exact @term. Qed.`
   That is, you have to give the full proof in one gulp, as a
   proof term (see Section :ref:`applyingtheorems`).

   .. warning::

      Use of this command is discouraged.  In particular, it
      doesn't work in Proof General because it must
      immediately follow the command that opened proof mode, but
      Proof General inserts :cmd:`Unset` :flag:`Silent` before it (see
      `Proof General issue #498
      <https://github.com/ProofGeneral/PG/issues/498>`_).

.. cmd:: Proof

   Is a no-op which is useful to delimit the sequence of tactic commands
   which start a proof, after a :cmd:`Theorem` command. It is a good practice to
   use :cmd:`Proof` as an opening parenthesis, closed in the script with a
   closing :cmd:`Qed`.

   .. seealso:: :cmd:`Proof with`

.. cmd:: Proof using @section_var_expr {? with @ltac_expr }

   .. insertprodn section_var_expr starred_ident_ref

   .. prodn::
      section_var_expr ::= {* @starred_ident_ref }
      | {? - } @section_var_expr50
      section_var_expr50 ::= @section_var_expr0 - @section_var_expr0
      | @section_var_expr0 + @section_var_expr0
      | @section_var_expr0
      section_var_expr0 ::= @starred_ident_ref
      | ()
      | ( @section_var_expr ) {? * }
      starred_ident_ref ::= @ident {? * }
      | Type {? * }
      | All

   Opens proof mode, declaring the set of
   :ref:`section <section-mechanism>` variables (see :ref:`gallina-assumptions`)
   used by the proof.
   These :ref:`proof annotations <proof-annotations>` are useful to enable asynchronous
   processing of proofs.  This :ref:`example <example-print-using>` shows how they work.
   The :cmd:`Qed` command verifies that the set of section variables
   used in the proof is a subset of the declared ones.

   The set of declared variables is closed under type dependency. For
   example, if ``T`` is a variable and ``a`` is a variable of type
   ``T``, then the commands ``Proof using a`` and ``Proof using T a``
   are equivalent.

   The set of declared variables always includes the variables used by
   the statement. In other words ``Proof using e`` is equivalent to
   ``Proof using Type + e`` for any declaration expression ``e``.

   :n:`- @section_var_expr50`
     Use all section variables except those specified by :n:`@section_var_expr50`

   :n:`@section_var_expr0 + @section_var_expr0`
     Use section variables from the union of both collections.
     See :ref:`nameaset` to see how to form a named collection.

   :n:`@section_var_expr0 - @section_var_expr0`
     Use section variables which are in the first collection but not in the
     second one.

   :n:`{? * }`
     Use the transitive closure of the specified collection.

   :n:`Type`
     Use only section variables occurring in the statement.  Specifying :n:`*`
     uses the forward transitive closure of all the section variables occurring
     in the statement. For example, if the variable ``H`` has type ``p < 5`` then
     ``H`` is in ``p*`` since ``p`` occurs in the type of ``H``.

   :n:`All`
     Use all section variables.

   .. warn:: @ident is both name of a Collection and Variable, Collection @ident takes precedence over Variable.

      If a specified name is ambiguous (it could be either a :cmd:`Collection` or a :cmd:`Variable`),
      then it is assumed to be a :cmd:`Collection` name.

   .. warn:: Variable All is shadowed by Collection named All containing all variables.

      This is variant of the previous warning for the **All** collection.

   .. seealso:: :ref:`tactics-implicit-automation`

.. attr:: using

   This :term:`attribute` can be applied to the :cmd:`Definition`, :cmd:`Example`,
   :cmd:`Fixpoint` and :cmd:`CoFixpoint` commands as well as to :cmd:`Lemma` and
   its variants.  It takes
   a :n:`@section_var_expr`, in quotes, as its value. This is equivalent to
   specifying the same :n:`@section_var_expr` in
   :cmd:`Proof using`.

   .. example::

      .. rocqtop:: all reset

         Section Test.
         Variable n : nat.
         Hypothesis Hn : n <> 0.

         #[using="Hn"]
         Lemma example : 0 < n.

      .. rocqtop:: in

         Abort.
         End Test.

.. _example-print-using:

   .. example :: Declaring section variables

      When a :ref:`section <section-mechanism>` is closed with :cmd:`End`, section
      variables declared with :cmd:`Proof using` are added to the theorem as
      additional variables.  You can see the effect on the theorem's statement
      with commands such as :cmd:`Check`, :cmd:`Print` and :cmd:`About` after the
      section is closed.  Currently there is no command that shows the section variables
      associated with a theorem before the section is closed.

      Adding the unnecessary section variable `radixNotZero` changes how `foo'` can be
      applied.

      .. rocqtop:: in

         Section bar.
           Variable radix : nat.
           Hypothesis radixNotZero : 0 < radix.

           Lemma foo : 0 = 0.
           Proof. reflexivity. Qed.

           Lemma foo' : 0 = 0.
           Proof using radixNotZero. reflexivity. Qed.  (* radixNotZero is not needed *)

      .. rocqtop:: all

           Print foo'.   (* Doesn't show radixNotZero yet *)
         End bar.
         Print foo.      (* Doesn't change after the End *)
         Print foo'.     (* "End" added type radix (used by radixNotZero) and radixNotZero *)
         Goal 0 = 0.

      .. rocqtop:: in

         Fail apply foo'.  (* Fails because of the extra variable *)

      .. rocqtop:: all

         apply (foo' 5).   (* Can be used if the extra variable is provided explicitly *)

      .. rocqtop:: abort none

Proof using options
```````````````````

The following options modify the behavior of ``Proof using``.


.. opt:: Default Proof Using "@section_var_expr"

   Set this :term:`option` to use :n:`@section_var_expr` as the
   default ``Proof using`` value. E.g. ``Set Default Proof Using "a
   b"`` will complete all ``Proof`` commands not followed by a
   ``using`` part with ``using a b``.

   Note that :n:`@section_var_expr` isn't validated immediately.  An
   invalid value will generate an error on a subsequent :cmd:`Proof`
   or :cmd:`Qed` command.


.. flag:: Suggest Proof Using

   When this :term:`flag` is on, :cmd:`Qed` suggests
   a ``using`` annotation if the user did not provide one.

..  _`nameaset`:

Name a set of section hypotheses for ``Proof using``
````````````````````````````````````````````````````

.. cmd:: Collection @ident := @section_var_expr

   This can be used to name a set of section
   hypotheses, with the purpose of making ``Proof using`` annotations more
   compact.

   .. example::

      Define the collection named ``Some`` containing ``x``, ``y`` and ``z``::

         Collection Some := x y z.

      Define the collection named ``Fewer`` containing only ``x`` and ``y``::

         Collection Fewer := Some - z

      Define the collection named ``Many`` containing the set union or set
      difference of ``Fewer`` and ``Some``::

         Collection Many := Fewer + Some
         Collection Many := Fewer - Some

      Define the collection named ``Many`` containing the set difference of
      ``Fewer`` and the unnamed collection ``x y``::

         Collection Many := Fewer - (x y)

   .. deprecated:: 8.15

      Redefining a collection, defining a collection with the same name as a variable,
      and invoking the :cmd:`Proof using` command when collection and variable names overlap
      are deprecated. See the warnings below and in the :cmd:`Proof using` command.

   .. exn:: "All" is a predefined collection containing all variables. It can't be redefined.

      When issuing a :cmd:`Proof using` command, **All** used as a collection name always means
      "use all variables".

   .. warn:: New Collection definition of @ident shadows the previous one.

      Redefining a :cmd:`Collection` overwrites the previous definition.

   .. warn:: @ident was already a defined Variable, the name @ident will refer to Collection when executing "Proof using" command.

      The :cmd:`Proof using` command allows specifying both :cmd:`Collection` and
      :cmd:`Variable` names. In case of ambiguity, a name is assumed to be Collection name.

Proof modes
-----------

When entering proof mode through commands such as :cmd:`Goal` and :cmd:`Proof`,
Rocq picks by default the |Ltac| mode. Nonetheless, there exist other proof modes
shipped in the standard Rocq installation, and furthermore some plugins define
their own proof modes. The default proof mode used when opening a proof can
be changed using the following option.

.. opt:: Default Proof Mode @string

   This :term:`option` selects the proof mode to use when starting a proof. Depending on the proof
   mode, various syntactic constructs are allowed when writing a
   proof. All proof modes support commands; the proof mode determines
   which tactic language and set of tactic definitions are available.  The
   possible option values are:

   `"Classic"`
     Activates the |Ltac| language and the tactics with the syntax documented
     in this manual.
     Some tactics are not available until the associated plugin is loaded,
     such as `SSR` or `micromega`.
     This proof mode is set when the :term:`prelude` is loaded.

   `"Noedit"`
     No tactic
     language is activated at all. This is the default when the :term:`prelude`
     is not loaded, e.g. through the `-noinit` option for `rocq`.

   `"Ltac2"`
     Activates the Ltac2 language and the Ltac2-specific variants of the documented
     tactics.
     This value is only available after :cmd:`Requiring <Require>` Ltac2.
     :cmd:`Importing <Import>` Ltac2 sets this mode.

   Some external plugins also define their own proof mode, which can be
   activated with this command.

.. cmd:: Proof Mode @string

   Sets the proof mode within the current proof.

Managing goals
--------------

.. cmd:: Undo {? {? To } @natural }

   Cancels the effect of the last :token:`natural` commands or tactics.
   The :n:`To @natural` form goes back to the specified state number.
   If :token:`natural` is not specified, the command goes back one command or tactic.

.. cmd:: Restart

   Restores the proof to the original goal.

   .. exn:: No focused proof to restart.
      :undocumented:

.. _focused_goals:

Focusing goals
``````````````

:gdef:`Focusing <focus>` lets you limit the context display to (initially) a
single goal.  If a tactic creates additional goals from a focused goal, the
subgoals are also focused.  The two focusing constructs are
:ref:`curly braces <curly-braces>` (`{` and `}`) and :ref:`bullets <bullets>`
(e.g. `-`, `+` or `*`).  These constructs can be nested.

.. _curly-braces:

Curly braces
~~~~~~~~~~~~

.. tacn:: {? {| @natural | [ @ident ] } : } %{
          %}
   :name: {; }

   .. todo
      See https://github.com/coq/coq/issues/12004 and
      https://github.com/coq/coq/issues/12825.

   ``{`` (without a terminating period) focuses on the first
   goal.  The subproof can only be
   unfocused when it has been fully solved (*i.e.*, when there is no
   focused goal left). Unfocusing is then handled by ``}`` (again, without a
   terminating period). See also an example in the next section.

   Note that when a focused goal is proved a message is displayed
   together with a suggestion about the right bullet or ``}`` to unfocus it
   or focus the next goal.

   :n:`@natural:`
     Focuses on the :token:`natural`\-th goal to prove.

.. _focus_shelved_goal:

   :n:`[ @ident ]: %{`
     Focuses on the goal named :token:`ident` even if the goal is not in focus.
     Goals are :term:`existential variables <existential variable>`, which don't
     have names by default.  You can give a name to a goal by using
     :n:`refine ?[@ident]`.

   .. example:: Working with named goals

      .. rocqtop:: in

         Ltac name_goal name := refine ?[name].  (* for convenience *)
         Set Printing Goal Names.  (* show goal names, e.g. "(?base)" and "(?step)" *)

      .. rocqtop:: all

         Goal forall n, n + 0 = n.
         Proof.
         induction n; [ name_goal base | name_goal step ].
         (* focus on the goal named "base" *)
         [base]: {
           reflexivity.

      .. rocqtop:: in

         }

      This can also be a way of focusing on a shelved goal, for instance:

      .. rocqtop:: all reset

         Goal exists n : nat, n = n.
         eexists ?[x].
         reflexivity.
         [x]: exact 0.
         Qed.

   .. exn:: This proof is focused, but cannot be unfocused this way.

      You are trying to use ``}`` but the current subproof has not been fully solved.

   .. exn:: No such goal (@natural).
      :undocumented:

   .. exn:: No such goal (@ident).
      :undocumented:

   .. exn:: Brackets do not support multi-goal selectors.

      Brackets are used to focus on a single goal given either by its position
      or by its name if it has one.

   .. seealso:: The error messages for bullets below.

.. _bullets:

Bullets
~~~~~~~

Alternatively, proofs can be structured with bullets instead of ``{`` and ``}``. The
first use of a bullet ``b`` focuses on the first goal ``g``.  The
same bullet can't be used again until the proof of ``g`` is completed,
then the next goal must be focused with another ``b``. Thus,
all the goals present just before the first use of the bullet must be focused with the
same bullet ``b``. See the example below.

Different bullets can be used to nest levels. The scope of each bullet
is limited to the enclosing ``{`` and ``}``, so bullets can be reused as further
nesting levels provided they are delimited by curly braces.  A :production:`bullet`
is made from ``-``, ``+`` or ``*`` characters (with no spaces and no period afterward):

.. tacn:: {| {+ - } | {+ + } | {+ * } }
   :undocumented:
   :name: bullet (- + *)

When a focused goal is proved, Rocq displays a message suggesting use of
``}`` or the correct matching bullet to unfocus the goal or focus the next subgoal.

.. note::

   In Proof General (``Emacs`` interface to Rocq), you must use
   bullets with the priority ordering shown above to have correct
   indentation. For example ``-`` must be the outer bullet and ``+`` the inner
   one in the example below.

.. example:: Use of bullets

  For the sake of brevity, the output for this example is summarized in comments.
  Note that the tactic following a bullet is frequently put on the same line with the bullet.
  Observe that this proof still works even if all the bullets in it are omitted.

  .. rocqtop:: in

    Goal (1=1 /\ 2=2) /\ 3=3.
    Proof.
    split.     (*     1 = 1 /\ 2 = 2 and 3 = 3 *)
    -          (* 1 = 1 /\ 2 = 2 *)
     split.    (*    1 = 1 and 2 = 2 *)
     +         (* 1 = 1 *)
      trivial.  (* subproof complete *)
     +         (* 2 = 2 *)
      trivial.  (* subproof complete *)
    -          (* 3 = 3 *)
     trivial.  (*  No more subgoals *)
    Qed.

.. exn:: Wrong bullet @bullet__1: Current bullet @bullet__2 is not finished.

   Before using bullet :n:`@bullet__1` again, you should first finish proving
   the current focused goal.
   Note that :n:`@bullet__1` and :n:`@bullet__2` may be the same.

.. exn:: Wrong bullet @bullet__1: Bullet @bullet__2 is mandatory here.

   You must put :n:`@bullet__2` to focus on the next goal. No other bullet is
   allowed here.

.. exn:: No such goal. Focus next goal with bullet @bullet.

   You tried to apply a tactic but no goals were under focus.
   Using :n:`@bullet` is  mandatory here.

.. exn:: No such goal. Try unfocusing with %}.

   You just finished a goal focused by ``{``, you must unfocus it with ``}``.

.. note:: Use :opt:`Default Goal Selector` with the ``!`` selector to force
   the use of focusing mechanisms (bullets, braces) and goal selectors so
   that it is always explicit to which goal(s) a tactic is applied.

.. opt:: Bullet Behavior {| "None" | "Strict Subproofs" }

   This :term:`option` controls the bullet behavior and can take two possible values:

   - "None": this makes bullets inactive.
   - "Strict Subproofs": this makes bullets active (this is the default behavior).

Other focusing commands
~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Unfocused

   Succeeds if there are no unfocused goals.  Otherwise the command fails.

.. cmd:: Focus {? @natural }

   Focuses the attention on the first goal to prove or, if :token:`natural` is
   specified, the :token:`natural`\-th.  The
   printing of the other goals is suspended until the focused goal
   is solved or unfocused.

   .. deprecated:: 8.8

      Prefer the use of bullets or focusing braces with a goal selector (see above).

.. cmd:: Unfocus

   Restores to focus the goals that were suspended by the last :cmd:`Focus` command.

   .. deprecated:: 8.8

.. _shelved_goals:

Shelving goals
``````````````

Goals can be :gdef:`shelved` so they are no longer displayed in the proof state.
Shelved goals can be unshelved with the :cmd:`Unshelve` command, which
makes all shelved goals visible in the proof state.  You can use
the goal selector :n:`[ @ident ]: %{` to focus on a single shelved goal
(see :ref:`here <focus_shelved_goal>`).  Currently there's no single command or
tactic that unshelves goals by name.

.. tacn:: shelve

   Moves the focused goals to the shelf.  They will no longer be displayed in
   the context.  The :cmd:`Show Existentials` command will still show
   these goals, which will be marked "(shelved)".

.. tacn:: shelve_unifiable

   Shelves only the goals under focus that are mentioned in other goals.
   Goals that appear in the type of other goals can be solved by unification.

   .. example:: shelve_unifiable

      .. rocqtop:: all abort

         Goal exists n, n=0.
         refine (ex_intro _ _ _).
         all: shelve_unifiable.
         reflexivity.

.. cmd:: Unshelve

   This command moves all the goals on the shelf (see :tacn:`shelve`)
   from the shelf into focus, by appending them to the end of the current
   list of focused goals.

.. tacn:: unshelve @ltac_expr1

   Performs :n:`@tactic`, then unshelves existential variables added to the
   shelf by the execution of :n:`@tactic`, prepending them to the current goal.

.. tacn:: admit
          give_up

   Allows skipping a subgoal to permit further progress on the rest of the
   proof.  The selected goals are removed from the context.  They are not
   solved and cannot be solved later in the proof. Since the goals are not
   solved, the proof cannot be closed with :cmd:`Qed` but only with :cmd:`Admitted`.

Reordering goals
````````````````

.. tacn:: cycle @int_or_var

   Reorders the selected goals so that the first :n:`@integer` goals appear after the
   other selected goals.
   If :n:`@integer` is negative, it puts the last :n:`@integer` goals at the
   beginning of the list.
   The tactic is only useful with a goal selector, most commonly `all:`.
   Note that other selectors reorder goals; `1,3: cycle 1` is not equivalent
   to `all: cycle 1`.  See :tacn:`… : … (goal selector)`.

   .. example:: cycle

      .. rocqtop:: none reset

         Parameter P : nat -> Prop.

      .. rocqtop:: in abort

         Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
         repeat split.    (*  P 1, P 2, P 3, P 4, P 5 *)
         all: cycle 2.    (*  P 3, P 4, P 5, P 1, P 2 *)
         all: cycle -3.   (* P 5, P 1, P 2, P 3, P 4 *)

.. tacn:: swap @int_or_var @int_or_var

   Exchanges the position of the specified goals.
   Negative values for :n:`@integer` indicate counting goals
   backward from the end of the list of selected goals. Goals are indexed from 1.
   The tactic is only useful with a goal selector, most commonly `all:`.
   Note that other selectors reorder goals; `1,3: swap 1 3` is not equivalent
   to `all: swap 1 3`.  See :tacn:`… : … (goal selector)`.

   .. example:: swap

      .. rocqtop:: in abort

         Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
         repeat split.    (*   P 1, P 2, P 3, P 4, P 5 *)
         all: swap 1 3.   (*  P 3, P 2, P 1, P 4, P 5 *)
         all: swap 1 -1.  (* P 5, P 2, P 1, P 4, P 3 *)

.. tacn:: revgoals

   Reverses the order of the selected goals.  The tactic is only useful with a goal
   selector, most commonly `all :`.   Note that other selectors reorder goals;
   `1,3: revgoals` is not equivalent to `all: revgoals`.  See :tacn:`… : … (goal selector)`.

   .. example:: revgoals

      .. rocqtop:: in abort

         Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
         repeat split.    (*  P 1, P 2, P 3, P 4, P 5 *)
         all: revgoals.   (* P 5, P 4, P 3, P 2, P 1 *)

Proving a subgoal as a separate lemma: abstract
-----------------------------------------------

.. tacn:: abstract @ltac_expr2 {? using @ident__name }

   Does a :tacn:`solve` :n:`[ @ltac_expr2 ]` and saves the subproof as an auxiliary lemma.
   if :n:`@ident__name` is specified, the lemma is saved with that name; otherwise
   the lemma is saved with the name :n:`@ident`\ `_subproof`\ :n:`{? @natural }` where
   :token:`ident` is the name of the current goal (e.g. the theorem name) and :token:`natural`
   is chosen to get a fresh name.  If the proof is closed with :cmd:`Qed`, the auxiliary lemma
   is inlined in the final proof term.

   This is useful with tactics such as
   :tacn:`discriminate` that generate huge proof terms with many intermediate
   goals.  It can significantly reduce peak memory use.  In most cases it doesn't
   have a significant impact on run time.  One case in which it can reduce run time
   is when a tactic `foo` is known to always pass type checking when it
   succeeds, such as in reflective proofs.  In this case, the idiom
   ":tacn:`abstract` :tacn:`exact_no_check` `foo`" will save half the type
   checking type time compared to ":tacn:`exact` `foo`".

   :tacn:`abstract` is an :token:`l3_tactic`.

   .. warning::

      The abstract tactic, while very useful, still has some known
      limitations.  See `#9146 <https://github.com/coq/coq/issues/9146>`_ for more
      details. We recommend caution when using it in some
      "non-standard" contexts. In particular, ``abstract`` doesn't
      work properly when used inside quotations ``ltac:(...)``.
      If used as part of typeclass resolution, it may produce incorrect
      terms when in polymorphic universe mode.

   .. warning::

      Provide :n:`@ident__name` at your own risk; explicitly named and reused subterms
      don’t play well with asynchronous proofs.

   .. tacn:: transparent_abstract @ltac_expr3 {? using @ident }

      Like :tacn:`abstract`, but save the subproof in a transparent lemma with a name in
      the form :n:`@ident`\ :n:`_subterm`\ :n:`{? @natural }`.

      .. warning::

         Use this feature at your own risk; building computationally relevant terms
         with tactics is fragile, and explicitly named and reused subterms
         don’t play well with asynchronous proofs.

      .. exn:: Proof is not complete.
         :name: Proof is not complete. (abstract)
         :undocumented:

.. _requestinginformation:

Requesting information
----------------------


.. cmd:: Show {? {| @ident | @natural } }

   Displays the current goals.

   :n:`@natural`
     Display only the :token:`natural`\-th goal.

   :n:`@ident`
     Displays the named goal :token:`ident`. This is useful in
     particular to display a shelved goal but only works if the
     corresponding existential variable has been named by the user
     (see :ref:`existential-variables`) as in the following example.

     .. example::

        .. rocqtop:: all abort

           Goal exists n, n = 0.
           eexists ?[n].
           Show n.

   .. exn:: No focused proof.
      :undocumented:

   .. exn:: No such goal.
      :undocumented:

.. cmd:: Show Proof {? Diffs {? removed } }

   Displays the proof term generated by the tactics
   that have been applied so far. If the proof is incomplete, the term
   will contain holes, which correspond to subterms which are still to be
   constructed. Each hole is an existential variable, which appears as a
   question mark followed by an identifier.

   Specifying “Diffs” highlights the difference between the
   current and previous proof step.  By default, the command shows the
   output once with additions highlighted.  Including “removed” shows
   the output twice: once showing removals and once showing additions.
   It does not examine the :opt:`Diffs` option.  See :ref:`showing_proof_diffs`.

.. cmd:: Show Conjectures

   Prints the names of all the
   theorems that are currently being proved. As it is possible to start
   proving a previous lemma during the proof of a theorem, there may
   be multiple names.

.. cmd:: Show Intro

   If the current goal begins by at least one product,
   prints the name of the first product as it would be
   generated by an anonymous :tacn:`intro`. The aim of this command is to ease
   the writing of more robust scripts. For example, with an appropriate
   Proof General macro, it is possible to transform any anonymous :tacn:`intro`
   into a qualified one such as ``intro y13``. In the case of a non-product
   goal, it prints nothing.

.. cmd:: Show Intros

   Similar to the previous command.
   Simulates the naming process of :tacn:`intros`.

.. cmd:: Show Existentials

   Displays all open goals / existential variables in the current proof
   along with the context and type of each variable.

.. cmd:: Show Match @qualid

   Displays a template of the Gallina :token:`match<term_match>`
   construct with a branch for each constructor of the type
   :token:`qualid`.  This is used internally by
   `company-coq <https://github.com/cpitclaudel/company-coq>`_.

   .. example::

      .. rocqtop:: all

         Show Match nat.

   .. exn:: Unknown inductive type.
      :undocumented:

.. cmd:: Show Universes

   Displays the set of all universe constraints and
   its normalized form at the current stage of the proof, useful for
   debugging universe inconsistencies.

.. cmd:: Show Goal @natural at @natural

   Available in `rocq repl`.  Displays a goal at a
   proof state using the goal ID number and the proof state ID number.
   It is primarily for use by tools such as Prooftree that need to fetch
   goal history in this way.  Prooftree is a tool for visualizing a proof
   as a tree that runs in Proof General.

.. cmd:: Guarded

   Some tactics (e.g. :tacn:`refine`) allow to build proofs using
   fixpoint or cofixpoint constructions. Due to the incremental nature
   of proof construction, the check of the termination (or
   guardedness) of the recursive calls in the fixpoint or cofixpoint
   constructions is postponed to the time of the completion of the proof.

   The command :cmd:`Guarded` allows checking if the guard condition for
   fixpoint and cofixpoint is violated at some time of the construction
   of the proof without having to wait the completion of the proof.

.. cmd:: Validate Proof

   Checks that the current partial proof is well-typed.
   It is useful for finding tactic bugs since without it, such errors will only be detected at :cmd:`Qed` time.

   It does not check the guard condition.  Use :cmd:`Guarded` for that.

.. _showing_diffs:

Showing differences between proof steps
---------------------------------------

Rocq can automatically highlight the differences between successive proof steps
and between values in some error messages.  Rocq can also highlight differences
in the proof term.
For example, the following screenshots of RocqIDE and coqtop show the application
of the same :tacn:`intros` tactic.  The tactic creates two new hypotheses, highlighted in green.
The conclusion is entirely in pale green because although it’s changed, no tokens were added
to it.  The second screenshot uses the "removed" option, so it shows the conclusion a
second time with the old text, with deletions marked in red.  Also, since the hypotheses are
new, no line of old text is shown for them.

.. comment screenshot produced with:
   Inductive ev : nat -> Prop :=
   | ev_0 : ev 0
   | ev_SS : forall n : nat, ev n -> ev (S (S n)).

   Fixpoint double (n:nat) :=
     match n with
     | O => O
     | S n' => S (S (double n'))
     end.

   Goal forall n, ev n -> exists k, n = double k.
   intros n E.

..

  .. image:: ../../_static/diffs-rocqide-on.png
     :alt: RocqIDE with Set Diffs on

..

  .. image:: ../../_static/diffs-rocqide-removed.png
     :alt: RocqIDE with Set Diffs removed

..

  .. image:: ../../_static/diffs-coqtop-on3.png
     :alt: coqtop with Set Diffs on

This image shows an error message with diff highlighting in RocqIDE:

..

  .. image:: ../../_static/diffs-error-message.png
     :alt: RocqIDE error message with diffs

How to enable diffs
```````````````````

.. opt:: Diffs {| "on" | "off" | "removed" }

   This :term:`option` is used to enable diffs.
   The “on” setting highlights added tokens in green, while the “removed” setting
   additionally reprints items with removed tokens in red.  Unchanged tokens in
   modified items are shown with pale green or red.  Diffs in error messages
   use red and green for the compared values; they appear regardless of the setting.
   (Colors are user-configurable.)

For `rocq repl`, showing diffs can be enabled when starting `rocq repl` with the
``-diffs on|off|removed`` command-line option or by setting the :opt:`Diffs` option
within Rocq.  You will need to provide the ``-color on|auto`` command-line option when
you start `rocq repl` in either case.

Colors for `rocq repl` can be configured by setting the ``ROCQ_COLORS`` environment
variable.  See section :ref:`customization-by-environment-variables`.  Diffs
use the tags ``diff.added``, ``diff.added.bg``, ``diff.removed`` and ``diff.removed.bg``.

In RocqIDE, diffs should be enabled from the ``View`` menu.  Don’t use the ``Set Diffs``
command in RocqIDE.  You can change the background colors shown for diffs from the
``Edit | Preferences | Tags`` panel by changing the settings for the ``diff.added``,
``diff.added.bg``, ``diff.removed`` and ``diff.removed.bg`` tags.  This panel also
lets you control other attributes of the highlights, such as the foreground
color, bold, italic, underline and strikeout.

Proof General, VsCoq and Coqtail can also display Rocq-generated proof diffs automatically.
Please see the PG documentation section
`"Showing Proof Diffs" <https://proofgeneral.github.io/doc/master/userman/Coq-Proof-General#Showing-Proof-Diffs>`_
and Coqtail's `"Proof Diffs" <https://github.com/whonore/Coqtail#proof-diffs>`_
for details.

How diffs are calculated
````````````````````````

Diffs are calculated as follows:

1. Select the old proof state to compare to, which is the proof state before
   the last tactic that changed the proof.  Changes that only affect the view
   of the proof, such as ``all: swap 1 2``, are ignored.

2. For each goal in the new proof state, determine what old goal to compare
   it to—the one it is derived from or is the same as.  Match the hypotheses by
   name (order is ignored), handling compacted items specially.

3. For each hypothesis and conclusion (the “items”) in each goal, pass
   them as strings to the lexer to break them into tokens.  Then apply the
   Myers diff algorithm :cite:`Myers` on the tokens and add appropriate highlighting.

Notes:

* Aside from the highlights, output for the "on" option should be identical
  to the undiffed output.
* Goals completed in the last proof step will not be shown even with the
  "removed" setting.

.. comment The following screenshots show diffs working with multiple goals and with compacted
   hypotheses.  In the first one, notice that the goal ``P 1`` is not highlighted at
   all after the split because it has not changed.

    .. todo: Use this script and remove the screenshots when ROCQ_COLORS
      works for coqtop in sphinx
    .. rocqtop:: none

      Set Diffs "on".
      Parameter P : nat -> Prop.
      Goal P 1 /\ P 2 /\ P 3.

    .. rocqtop:: out

      split.

    .. rocqtop:: all abort

      2: split.

  ..

    .. rocqtop:: none

      Set Diffs "on".
      Goal forall n m : nat, n + m = m + n.
      Set Diffs "on".

    .. rocqtop:: out

       intros n.

    .. rocqtop:: all abort

      intros m.

This screenshot shows the result of applying a :tacn:`split` tactic that replaces one goal
with 2 goals.  Notice that the goal ``P 1`` is not highlighted at all after
the split because it has not changed.

..

  .. image:: ../../_static/diffs-rocqide-multigoal.png
     :alt: rocqide with Set Diffs on with multiple goals

Diffs may appear like this after applying a :tacn:`intro` tactic that results
in a compacted hypotheses:

..

  .. image:: ../../_static/diffs-rocqide-compacted.png
     :alt: rocqide with Set Diffs on with compacted hypotheses

.. _showing_proof_diffs:

"Show Proof" differences
````````````````````````

To show differences in the proof term:

- In `rocq repl` and Proof General, use the :cmd:`Show Proof` `Diffs` command.

- In RocqIDE, position the cursor on or just after a tactic to compare the proof term
  after the tactic with the proof term before the tactic, then select
  `View / Show Proof` from the menu or enter the associated key binding.
  Differences will be shown applying the current `Show Diffs` setting
  from the `View` menu.  If the current setting is `Don't show diffs`, diffs
  will not be shown.

  Output with the "added and removed" option looks like this:

  ..

    .. image:: ../../_static/diffs-show-proof.png
       :alt: rocqide with Set Diffs on with compacted hypotheses

Delaying solving unification constraints
----------------------------------------

.. tacn:: solve_constraints
   :undocumented:

.. flag:: Solve Unification Constraints

   By default, after each tactic application, postponed typechecking unification
   problems are resolved using heuristics. Unsetting this :term:`flag` disables this
   behavior, allowing tactics to leave unification constraints unsolved. Use the
   :tacn:`solve_constraints` tactic at any point to solve the constraints.

.. _proof-maintenance:

Proof maintenance
-----------------

*Experimental.*  Many tactics, such as :tacn:`intros`, can automatically generate names, such
as "H0" or "H1" for a new hypothesis introduced from a goal.  Subsequent proof steps
may explicitly refer to these names.  However, future versions of Rocq may not assign
names exactly the same way, which could cause the proof to fail because the
new names don't match the explicit references in the proof.

The following :flag:`Mangle Names` settings let users find all the
places where proofs rely on automatically generated names, which can
then be named explicitly to avoid any incompatibility.  These
settings cause Rocq to generate different names, producing errors for
references to automatically generated names.

.. flag:: Mangle Names

   When this :term:`flag` is set (it is off by default),
   generated names use the prefix specified in the following
   option instead of the default prefix.

.. opt:: Mangle Names Prefix @string

   This :term:`option` specifies the prefix to use when generating names.

.. flag:: Mangle Names Light

   When this :term:`flag` is set (it is off by default),
   the names generated by :flag:`Mangle Names` only add
   the :opt:`Mangle Names Prefix` to the original name.

Controlling proof mode
----------------------


.. opt:: Hyps Limit @natural

   This :term:`option` controls the maximum number of hypotheses displayed in goals
   after the application of a tactic. All the hypotheses remain usable
   in the proof development.
   When unset, it goes back to the default mode which is to print all
   available hypotheses.


.. flag:: Nested Proofs Allowed

   When turned on (it is off by default), this :term:`flag` enables support for nested
   proofs: a new assertion command can be inserted before the current proof is
   finished, in which case Rocq will temporarily switch to the proof of this
   *nested lemma*. When the proof of the nested lemma is finished (with :cmd:`Qed`
   or :cmd:`Defined`), its statement will be made available (as if it had been
   proved before starting the previous proof) and Rocq will switch back to the
   proof of the previous assertion.

.. flag:: Printing Goal Names

   When this :term:`flag` is turned on, the name of the goal is printed in
   proof mode, which can be useful in cases of cross references
   between goals.

.. flag:: Printing Goal Tags

   Internal flag used to implement Proof General's proof-tree mode.

Controlling memory usage
------------------------

.. cmd:: Print Debug GC

   Prints heap usage statistics, which are values from the `stat` type of the `Gc` module
   described
   `here <https://caml.inria.fr/pub/docs/manual-ocaml/libref/Gc.html#TYPEstat>`_
   in the OCaml documentation.
   The `live_words`, `heap_words` and `top_heap_words` values give the basic information.
   Words are 8 bytes or 4 bytes, respectively, for 64- and 32-bit executables.

When experiencing high memory usage the following commands can be used
to force Rocq to optimize some of its internal data structures.

.. cmd:: Optimize Proof

   Shrink the data structure used to represent the current proof.


.. cmd:: Optimize Heap

   Perform a heap compaction.  This is generally an expensive operation.
   See: `OCaml Gc.compact <http://caml.inria.fr/pub/docs/manual-ocaml/libref/Gc.html#VALcompact>`_
   There is also an analogous tactic :tacn:`optimize_heap`.

Memory usage parameters can be set through the :ref:`OCAMLRUNPARAM <OCAMLRUNPARAM>`
environment variable.
