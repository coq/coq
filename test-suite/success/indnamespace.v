Module InductiveProper.

Module A.
#[namespace=proper]
Inductive myunit := mytt.
Fail Check mytt.
Check myunit.mytt.
End A.

Fail Check mytt.
Fail Check myunit.mytt.
Check A.myunit.mytt.

Import A.

Fail Check mytt.
Check myunit.mytt.
Check A.myunit.mytt.

End InductiveProper.

Module InductiveBoth.

Module A.
#[namespace=both]
Inductive myunit := mytt.
Check mytt.
Check myunit.mytt.
End A.

Fail Check mytt.
Fail Check myunit.mytt.
Check A.myunit.mytt.

Import A.

Check mytt.
Check myunit.mytt.
Check A.myunit.mytt.

End InductiveBoth.
