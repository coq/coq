Module Type S. End S.

Declare Module M : S.

Module Type F (T: S). End F.

Fail Module Type N := F with Module T := M.
