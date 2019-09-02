- Fix soundness issue with template polymorphism (`#9294
  <https://github.com/coq/coq/issues/9294>`_)

  Declarations of template-polymorphic inductive types ignored the
  provenance of the universes they were abstracting on and did not
  detect if they should be greater or equal to :math:`\Set` in
  general. Previous universes and universes introduced by the inductive
  definition could have constraints that prevented their instantiation
  with e.g. :math:`\Prop`, resulting in unsound instantiations later. The
  implemented fix only allows abstraction over universes introduced by
  the inductive declaration, and properly records all their constraints
  by making them by default only :math:`>= \Prop`. It is also checked
  that a template polymorphic inductive actually is polymorphic on at
  least one universe.

  This prevents inductive declarations in sections to be universe
  polymorphic over section parameters. For a backward compatible fix,
  simply hoist the inductive definition out of the section.
  An alternative is to declare the inductive as universe-polymorphic and
  cumulative in a universe-polymorphic section: all universes and
  constraints will be properly gathered in this case.
  See :ref:`Template-polymorphism` for a detailed exposition of the
  rules governing template-polymorphic types.

  To help users incrementally fix this issue, a command line option
  `-no-template-check` and a global flag :flag:`Template Check` are
  available to selectively disable the new check. Use at your own risk.

  (`#9918 <https://github.com/coq/coq/pull/9918>`_, by Matthieu Sozeau
  and Maxime Dénès).
