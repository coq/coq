Require A.
Notation "!!" := A.x : foo_scope.
Fail Check A.def !!.

Import A.
Check def ##.
