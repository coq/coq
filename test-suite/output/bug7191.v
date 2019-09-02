Require Extraction.
Definition f (x : False) : unit -> unit := match x with end.
Recursive Extraction f.
