- **Fixed:**
  `rocq dep` implicitly adds `-I $rocq-runtime/..` after the explicit `-I` instead of before
  (where `$rocq-runtime` is the expected location of the rocq-runtime package).
  This means that if a local plugin (whose META is in an explicit `-I` path) is installed next to rocq-runtime,
  `rocq dep` will emit a dependency on the local version instead of the installed version
  (`#20393 <https://github.com/coq/coq/pull/20393>`_,
  by Gaëtan Gilbert).
