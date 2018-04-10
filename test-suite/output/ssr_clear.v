Require Import ssreflect.

Example foo : True -> True.
Proof.
Fail move=> {NO_SUCH_NAME}.
Abort.
