(*"2" should not break the parsing of commands referring to "2" *)
Tactic Notation "foo" "2" := idtac.
Global Hint Extern 2 (True) => exact I : core.
