Structure S := {
  ssort :> Type;
  sstuff : ssort;
}.

Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.

Check nat : S.

Set Printing Coercions.

Check nat : S.

Set Printing All.

Check nat : S.
