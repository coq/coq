(** In this file, either all four [Check]s should fail, or all four should succeed. *)
Module A.
  Section HexStrings.
    Require Import String.
  End HexStrings.
  Fail Check string.
End A.

Module B.
  Section HexStrings.
    Require String.
    Import String.
  End HexStrings.
  Fail Check string.
End B.

Section HexStrings.
  Require String.
  Import String.
End HexStrings.
Fail Check string.

Section HexStrings'.
  Require Import String.
End HexStrings'.
Check string.
