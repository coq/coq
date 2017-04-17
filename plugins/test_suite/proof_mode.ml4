
open Pcoq
open Ltac_plugin
open Genarg

let test = Gram.entry_create "vernac:test"

let tac_class _= Vernac_classifier.classify_as_proofstep

(* TODO: replace by
     VERNAC TACTIC test EXTEND mytac
   once available
*)
VERNAC test EXTEND Mytac CLASSIFIED BY tac_class
[ "test" "." ] -> [ () ]
END

let () = register_tactic_entry "test" test
