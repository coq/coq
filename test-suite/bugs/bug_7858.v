Notation foo x := false.

Fail Check (match true with foo _ => 0 | _ => 1 end).

Notation bar x := (pair x).

Check match (0,1) with bar x y => x + y end.
Fail Check match (0,1) with bar x => x end.
Fail Check match (0,1) with bar => 0 end.
Fail Check match (0,1) with bar x y z => 0 end.
