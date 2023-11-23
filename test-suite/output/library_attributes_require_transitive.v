(* check that file deprecations are only printed on direct requirement *)
Require TestSuite.library_attributes_require.
(* but still printed on direct requirement even if the Require doesn't actually
   do anything (because file is already loaded) *)
Require TestSuite.library_attributes.
