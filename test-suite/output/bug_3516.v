Module A.
Module AA.
Notation foo := eq_refl.
Print foo.
About foo.
Check eq_refl 3.
Check foo 3.
End AA.

Module AB.
Notation foo2 := (@eq_refl _).
Print foo2.
About foo2.
Check foo2 3.
End AB.

Import AA.
Import AB.
Print foo.
Check foo.
Check foo2 _.
Check foo _.
About foo.
Print foo2.
About foo2.
End A.

Module B.
Definition id {A:Type} (a:A) {B:Type} (b:B) := (a,b).
Notation foo := (@id _ 2 _).
Print foo.
About foo.
Check id 2 3.
Check foo 3.

Notation foo2 := (id 2).
Print foo2.
About foo2.
Print foo.
About foo.
Check foo2 3.
End B.

Module MakeArgumentPrinted.
Notation expfoo x := (eq_refl x).
Check expfoo 3.
End MakeArgumentPrinted.
