(* check that file deprecations are only printed on direct requirement *)
Require TestSuite.requires_deprecated_library.
(* but still printed on direct requirement even if the Require doesn't actually
   do anything (because file is already loaded) *)
Require TestSuite.deprecated_library.
