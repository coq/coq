(** In this file, either both [Check]s should fail, or both should succeed. *)
Section HexStrings.
  Require String.
  Import String.
End HexStrings.
Fail Check string.

Section HexStrings'.
  Require Import String.
End HexStrings'.
Check string.
