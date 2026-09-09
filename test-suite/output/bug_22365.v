From Corelib Require Import Array.PrimArray Numbers.Cyclic.Int63.PrimInt63 extraction.Extraction.

Definition a3lit : PrimArray.array nat := [|0; 1; 2 | 4|].

Extraction a3lit.
