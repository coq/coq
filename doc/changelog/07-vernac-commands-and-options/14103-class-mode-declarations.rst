- **Added:**
  New attribute :attr:`modes` for :cmd:`Class` declarations,
  option :opt:`Typeclasses Default Mode` and warning
  :ref:`class-declaration-default-mode <TypeclassesDefaultModeWarning>`.
  The new attribute allows to set the :ref:`modes of resolution <ClassModes>`
  of a class at declaration time.
  The new option declares a default mode which will be used for *all* indices of
  declared classes. The new warning can be activated or even turned into an error
  if a library author prefers to require mode declarations on every class.
  (`#14103 <https://github.com/coq/coq/pull/14103>`_, by Matthieu Sozeau).
