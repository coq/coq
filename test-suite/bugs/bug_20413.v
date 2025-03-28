Fail Fixpoint F(sz c:nat)(f:nat->nat):nat :=
match sz with
| S sz0 =>
    F sz0 (S c) (fun sz' => F sz' 0 f)
| O => S (f c)
end.
