- **Changed:**
  Coq's configure script now defaults to `-native-compiler no`.
  Previously, the default was `-native-compiler ondemand`, except on
  Windows. The behavior for users installing through opam does not change,
  i.e., it is `-native-compiler no` if the `coq-native` package is not
  installed, and `-native-compiler yes` otherwise.
  (`#15494 <https://github.com/coq/coq/pull/15494>`_,
  by Théo Zimmermann).
- **Added:**
  Coq now supports OCaml 5; note that OCaml 5 is not compatible with
  Coq's native reduction machine
  (`#15494 <https://github.com/coq/coq/pull/15494>`_,
  by Emilio Jesus Gallego Arias, Gaëtan Gilbert, Guillaume Melquiond,
  Pierre-Marie Pédrot, and others).
