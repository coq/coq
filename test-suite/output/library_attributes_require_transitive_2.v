(* We have the second warning "deprecated-transitive-library-file"
   that always triggers (even on transitive requires) *)
Set Warnings "deprecated-transitive-library-file".
Set Warnings "warn-transitive-library-file".
Require TestSuite.requires_deprecated_library.
