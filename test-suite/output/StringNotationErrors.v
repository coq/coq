Require Import PrimInt63 PrimString.

Inductive smallstring := SmallString (_:string).

Declare Scope smallstring_scope.
Open Scope smallstring_scope.

Module V1.

  Definition of_smallstring '(SmallString v) := v.


  Definition to_smallstring v :=
    if PrimInt63.leb (length v) 10 then Ok (SmallString v)
    else Error (cat "not a small string: " v).

  String Notation smallstring to_smallstring of_smallstring : smallstring_scope.

  Check "hello".

  Fail Check "too long string".

  (* printing function doesn't check so we print something that doesn't parse *)
  Check SmallString "too long string".

End V1.

Module V2.
  Inductive smallstring_error := NotSmallString (_:string).

  Definition to_smallstring v :=
    if PrimInt63.leb (length v) 10 then Ok (SmallString v)
    else Error (NotSmallString v).

  Definition of_smallstring '(SmallString v) :=
    match to_smallstring v with
    | Ok _ => Ok v
    | Error e => Error e
    end.

  String Notation smallstring to_smallstring of_smallstring : smallstring_scope.

  Check "hello".

  Fail Check "too long string".

  (* printing function produces an error message but its content is ignored *)
  Check SmallString "too long string".
End V2.
