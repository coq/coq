- **Fixed:**
  quadratic compilation time of chains of ``<+`` over functor module
  types (and, more generally, of repeated module subtyping checks
  against a large accumulated signature): the "Include Self" subtyping
  check now looks fields up in the environment on demand instead of
  eagerly strengthening and indexing the whole accumulated signature,
  and successful field checks are cached so that re-checking the same
  fields (e.g. against every prefix of a chain, or on repeated
  applications of the same functor) hits a fast path
  (`#22281 <https://github.com/rocq-prover/rocq/pull/22281>`_,
  fixes `#22279 <https://github.com/rocq-prover/rocq/issues/22279>`_,
  written by Claude (Anthropic), for Jason Gross).
