- **Fixed:**
  Fix the timeout facility on Unix to allow for nested timeouts.
  Previous behavior on nested timeouts was that an "inner" timeout would replace an "outer"
  timeout, so that the outer timeout would no longer fire. With the new behavior, Unix and Windows
  implementations should be (approximately) equivalent.
  (`#13586 <https://github.com/coq/coq/pull/13586>`_,
  by Lasse Blaauwbroek).
