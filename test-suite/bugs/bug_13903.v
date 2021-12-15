Section test.
Variables (T : Type) (x : T).
#[using="x"] Definition test : unit := tt.
End test.
Check test : forall T, T -> unit.
