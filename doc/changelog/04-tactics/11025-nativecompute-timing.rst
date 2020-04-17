- **Changed:** The :flag:`NativeCompute Timing` flag causes calls to
  :tacn:`native_compute` (as well as kernel calls to the native
  compiler) to emit separate timing information about conversion to
  native code, compilation, execution, and reification.  It replaces
  the timing information previously emitted when the `-debug` flag was
  set, and allows more fine-grained timing of the native compiler
  (`#11025 <https://github.com/coq/coq/pull/11025>`_, by Jason Gross).
  Additionally, the timing information now uses real time rather than
  user time (Fixes `#11962
  <https://github.com/coq/coq/issues/11962>`_, `#11963
  <https://github.com/coq/coq/pull/11963>`_, by Jason Gross)
