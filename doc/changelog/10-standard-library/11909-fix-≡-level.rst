- **Changed:**
  The level of :g:`≡` in ``Coq.Numbers.Cyclic.Int63.Int63`` is now 70,
  no associativity, in line with :g:`=`.  Note that this is a minor
  incompatibility with developments that declare their own :g:`≡`
  notation and import ``Int63`` (fixes `#11905
  <https://github.com/coq/coq/issues/11905>`_, `#11909
  <https://github.com/coq/coq/pull/11909>`_, by Jason Gross).
