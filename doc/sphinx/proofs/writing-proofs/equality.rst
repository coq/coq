Equality
--------


.. tacn:: f_equal
   :name: f_equal

   This tactic applies to a goal of the form :g:`f a`:sub:`1` :g:`... a`:sub:`n`
   :g:`= f′a′`:sub:`1` :g:`... a′`:sub:`n`.  Using :tacn:`f_equal` on such a goal
   leads to subgoals :g:`f=f′` and :g:`a`:sub:`1` = :g:`a′`:sub:`1` and so on up
   to :g:`a`:sub:`n` :g:`= a′`:sub:`n`. Amongst these subgoals, the simple ones
   (e.g. provable by :tacn:`reflexivity` or :tacn:`congruence`) are automatically
   solved by :tacn:`f_equal`.


.. tacn:: reflexivity
   :name: reflexivity

   This tactic applies to a goal that has the form :g:`t=u`. It checks that `t`
   and `u` are convertible and then solves the goal. It is equivalent to
   ``apply refl_equal``.

   .. exn:: The conclusion is not a substitutive equation.
      :undocumented:

   .. exn:: Unable to unify ... with ...
      :undocumented:


.. tacn:: symmetry
   :name: symmetry

   This tactic applies to a goal that has the form :g:`t=u` and changes it into
   :g:`u=t`.


.. tacv:: symmetry in @ident

   If the statement of the hypothesis ident has the form :g:`t=u`, the tactic
   changes it to :g:`u=t`.


.. tacn:: transitivity @term
   :name: transitivity

   This tactic applies to a goal that has the form :g:`t=u` and transforms it
   into the two subgoals :n:`t=@term` and :n:`@term=u`.

   .. tacv:: etransitivity

      This tactic behaves like :tacn:`transitivity`, using a fresh evar instead of
      a concrete :token:`term`.
