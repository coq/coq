- The :flag:`NativeCompute Timing` flag causes calls to
  :tacn:`native_compute` (as well as kernel calls to the native
  compiler) to emit separate timing information about compilation,
  execution, and reification.  It replaces the timing information
  previously emitted when the `-debug` flag was set, and allows more
  fine-grained timing of the native compiler.  (`#11023
  <https://github.com/coq/coq/pull/11023>`_, by Jason Gross).
