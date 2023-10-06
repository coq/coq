- **Changed:**
  In casts like :g:`term : t` where :g:`t` is bound to some
  scope :g:`t_scope`, via :cmd:`Bind Scope`, the :g:`term` is now
  interpreted in scope :g:`t_scope`. In particular when :g:`t`
  is :g:`Type` the :g:`term` is interpreted in :g:`type_scope`
  and when :g:`t` is a product the :g:`term` is interpreted
  in :g:`fun_scope`
  (`#6134 <https://github.com/coq/coq/pull/6134>`_,
  fixes `#14959 <https://github.com/coq/coq/issues/14959>`_,
  by Hugo Herbelin, reviewed by Maxime Dénès, Jim Fehrle, Emilio Gallego, Gaëtan Gilbert, Jason Gross, Pierre-Marie Pédrot, Pierre Roux, Bas Spitters and Théo Zimmermann).
