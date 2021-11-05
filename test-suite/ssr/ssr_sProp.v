Require Import ssreflect StrictProp.

Goal True.
have h := (fun x : sEmpty => x).
constructor.
Qed.
