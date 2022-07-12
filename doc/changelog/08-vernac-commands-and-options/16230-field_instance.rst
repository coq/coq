- **Added:**
  :g:`::` syntax to declare fields of records as :ref:`typeclass <typeclasses>` instances
  (`#16230 <https://github.com/coq/coq/pull/16230>`_,
  fixes `#16224 <https://github.com/coq/coq/issues/16224>`_,
  by Pierre Roux, reviewed by Ali Caglayan, Jim Fehrle, Gaëtan Gilbert
  and Pierre-Marie Pédrot).
- **Deprecated**
  :g:`:>` syntax, to declare fields of :ref:`typeclasses` as instances,
  since it is now replaced by :g:`::` (see :n:`@of_type_inst`).
  This will allow, in a future release, making :g:`:>` declare :ref:`coercions`
  as it does in :ref:`record <records>` definitions
  (`#16230 <https://github.com/coq/coq/pull/16230>`_,
  fixes `#16224 <https://github.com/coq/coq/issues/16224>`_,
  by Pierre Roux, reviewed by Ali Caglayan, Jim Fehrle, Gaëtan Gilbert
  and Pierre-Marie Pédrot).
