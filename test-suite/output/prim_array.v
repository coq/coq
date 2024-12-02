Primitive array := #array_type.
Set Debug "univMinim".
Check [| | 0 |].

Check [| 1; 2; 3 | 0 |].

Set Printing Universes.
Check [| | 0 |].

Check [| bool; list nat | nat |].
