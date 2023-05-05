Module Type T.

End T.

Module M : T.
  Require Import BinNums.
  Definition f := @positive.
End M.
