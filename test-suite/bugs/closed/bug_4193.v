Module Type E.
End E.

Module Type A (M : E).
End A.

Fail Module Type F (Import X : A).
