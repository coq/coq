.. tacn:: cycle @integer
   :name: cycle

   Reorders the selected goals so that the first :n:`@integer` goals appear after the
   other selected goals.
   If :n:`@integer` is negative, it puts the last :n:`@integer` goals at the
   beginning of the list.
   The tactic is only useful with a goal selector, most commonly `all:`.
   Note that other selectors reorder goals; `1,3: cycle 1` is not equivalent
   to `all: cycle 1`.  See :tacn:`… : … (goal selector)`.

.. example::

   .. coqtop:: none reset

      Parameter P : nat -> Prop.

   .. coqtop:: all abort

      Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
      repeat split.
      all: cycle 2.
      all: cycle -3.

.. tacn:: swap @integer @integer
   :name: swap

   Exchanges the position of the specified goals.
   Negative values for :n:`@integer` indicate counting goals
   backward from the end of the list of selected goals. Goals are indexed from 1.
   The tactic is only useful with a goal selector, most commonly `all:`.
   Note that other selectors reorder goals; `1,3: swap 1 3` is not equivalent
   to `all: swap 1 3`.  See :tacn:`… : … (goal selector)`.

.. example::

   .. coqtop:: all abort

      Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
      repeat split.
      all: swap 1 3.
      all: swap 1 -1.

.. tacn:: revgoals
   :name: revgoals

   Reverses the order of the selected goals.  The tactic is only useful with a goal
   selector, most commonly `all :`.   Note that other selectors reorder goals;
   `1,3: revgoals` is not equivalent to `all: revgoals`.  See :tacn:`… : … (goal selector)`.

   .. example::

      .. coqtop:: all abort

         Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
         repeat split.
         all: revgoals.

.. tacn:: shelve
   :name: shelve

   This tactic moves all goals under focus to a shelf. While on the
   shelf, goals will not be focused on. They can be solved by
   unification, or they can be called back into focus with the command
   :cmd:`Unshelve`.

   .. tacv:: shelve_unifiable
      :name: shelve_unifiable

      Shelves only the goals under focus that are mentioned in other goals.
      Goals that appear in the type of other goals can be solved by unification.

      .. example::

         .. coqtop:: all abort

            Goal exists n, n=0.
            refine (ex_intro _ _ _).
            all: shelve_unifiable.
            reflexivity.

.. cmd:: Unshelve

   This command moves all the goals on the shelf (see :tacn:`shelve`)
   from the shelf into focus, by appending them to the end of the current
   list of focused goals.

.. tacn:: unshelve @tactic
   :name: unshelve

   Performs :n:`@tactic`, then unshelves existential variables added to the
   shelf by the execution of :n:`@tactic`, prepending them to the current goal.

.. tacn:: give_up
   :name: give_up

   This tactic removes the focused goals from the proof. They are not
   solved, and cannot be solved later in the proof. As the goals are not
   solved, the proof cannot be closed.

   The ``give_up`` tactic can be used while editing a proof, to choose to
   write the proof script in a non-sequential order.
