Require Import String Extraction.

Definition str := "This is a string"%string.

(* Raw extraction of strings, in OCaml *)
Extraction Language OCaml.
Extraction str.

(* Raw extraction of strings, in Haskell *)
Extraction Language Haskell.
Extraction str.

(* Extraction to char list, in OCaml *)
Require Import ExtrOcamlString.
Extraction Language OCaml.
Extraction str.

(* Extraction to native strings, in OCaml *)
Require Import ExtrOcamlNativeString.
Extraction str.

(* Extraction to native strings, in Haskell *)
Require Import ExtrHaskellString.
Extraction Language Haskell.
Extraction str.
