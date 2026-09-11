(* There is intentionally no vernacular setter for [check_eliminations]:
   this test plugin toggles it directly, the way plugins such as
   rocq-lean-import do, so that the reporting of unchecked sort eliminations
   by Print Assumptions and rocqchk can be exercised. *)

let set_elimination_checking b =
  let flags = Global.typing_flags () in
  Global.set_typing_flags { flags with Declarations.check_eliminations = b }
