- **Added:**
  Support for better extraction of strings in OCaml and Haskell:
  `ExtOcamlNativeString` provides bindings from the Coq `String` type to
  the OCaml `string` type, and string literals can be extracted to literals,
  both in OCaml and Haskell. (`#10486
  <https://github.com/coq/coq/pull/10486>`_, by Xavier Leroy, with help from
  Maxime Dénès, review by Hugo Herbelin).
