- **Changed:**
  :cmd:`Hint Unfold` in discriminated databases now respects its
  specification, namely that a constant may be unfolded only when
  it is the head of the goal. The previous behavior was to perform
  unfolding on any goal, without any limitation.

  An unexpected side-effect of this was that a database that
  contained ``Unfold`` hints would sometimes trigger silent
  strong βι-normalization of the goal. Indeed, :tacn:`unfold`
  performs such a normalization regardless of the presence of its
  argument in the goal. This does introduce a bit of backwards
  incompatibility, but it occurs in very specific situations
  and is easily circumvented. Since by default hint bases
  are not discriminated, it means that incompatibilities are
  typically observed when adding unfold hints to the typeclass
  database.

  In order to recover the previous behavior, it is enough
  to replace instances of ``Hint Unfold foo.``
  with ``Hint Extern 4 => progress (unfold foo).``. A less compatible but
  finer-grained change can be achieved by only adding the missing normalization
  phase with ``Hint Extern 4 => progress (lazy beta iota).``.
  (`#14679 <https://github.com/coq/coq/pull/14679>`_,
  fixes `#14874 <https://github.com/coq/coq/issues/14874>`_,
  by Pierre-Marie Pédrot).
