Module M. Definition y := 4. End M.
Import M.

#[deprecated(use=y)]
Definition x := 3.

Module N. Definition y := 5. End N.
Import N.

Check x.