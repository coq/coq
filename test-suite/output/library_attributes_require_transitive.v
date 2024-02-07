(* check that file deprecations are only printed on direct requirement *)
Require TestSuite.requires_deprecated_library.
(* but still printed on direct requirement even if the Require doesn't actually
   do anything (because file is already loaded) *)
Require TestSuite.deprecated_library.

(* We have the second warning "deprecated-transitive-library-file"
   that always triggers (even on transitive requires) *)
Reset Initial.
Set Warnings "deprecated-transitive-library-file".
Set Warnings "warn-transitive-library-file".
Require TestSuite.requires_deprecated_library.
