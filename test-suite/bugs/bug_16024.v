Module Type T. End T.

Module F (E : T) := E.

Module FT (X:T). End FT.

Module M := F <+ FT.
