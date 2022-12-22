- **Changed:**
  Coq's configure script now defaults to `-native-compiler no`.
  Previously, the default was `-native-compiler ondemand`, except on
  Windows. The behavior for users installing through opam does not change,
  i.e., it is `-native-compiler no` if the `coq-native` package is not
  installed, and `-native-compiler yes` otherwise.
  (`#16997 <https://github.com/coq/coq/pull/16997>`_,
  by Théo Zimmermann).
- **Added:**
  Coq now supports OCaml 5; note that OCaml 5 is not compatible with
  Coq's native reduction machine
  (`#15494 <https://github.com/coq/coq/pull/15494>`_,
  `#16925 <https://github.com/coq/coq/pull/16925>`_,
  `#16947 <https://github.com/coq/coq/pull/16947>`_,
  `#16959 <https://github.com/coq/coq/pull/16959>`_,
  `#16988 <https://github.com/coq/coq/pull/16988>`_,
  `#16991 <https://github.com/coq/coq/pull/16991>`_,
  `#16996 <https://github.com/coq/coq/pull/16996>`_,
  `#16997 <https://github.com/coq/coq/pull/16997>`_,
  `#16999 <https://github.com/coq/coq/pull/16999>`_,
  `#17010 <https://github.com/coq/coq/pull/17010>`_, and
  `#17015 <https://github.com/coq/coq/pull/17015>`_)
  by Emilio Jesus Gallego Arias, Gaëtan Gilbert, Guillaume Melquiond,
  Pierre-Marie Pédrot, and others).
