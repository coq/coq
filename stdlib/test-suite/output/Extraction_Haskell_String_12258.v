From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrHaskellString.
Extraction Language Haskell.
Set Extraction File Comment "IMPORTANT: If you change this file, make sure that running [cp Extraction_Haskell_String_12258.out Extraction_Haskell_String_12258.hs && ghc -o test Extraction_Haskell_String_12258.hs] succeeds".
Inductive output_type_code :=
| ascii_dec
| ascii_eqb
| string_dec
| string_eqb
| byte_eqb
| byte_eq_dec
.

Definition output_type_sig (c : output_type_code) : { T : Type & T }
  := existT (fun T => T)
            _
            match c return match c with ascii_dec => _ | _ => _ end with
            | ascii_dec => Ascii.ascii_dec
            | ascii_eqb => Ascii.eqb
            | string_dec => String.string_dec
            | string_eqb => String.eqb
            | byte_eqb => Byte.eqb
            | byte_eq_dec => Byte.byte_eq_dec
            end.

Definition output_type (c : output_type_code)
  := Eval cbv [output_type_sig projT1 projT2] in
      projT1 (output_type_sig c).
Definition output (c : output_type_code) : output_type c
  := Eval cbv [output_type_sig projT1 projT2] in
      match c return output_type c with
      | ascii_dec as c
      | _ as c
        => projT2 (output_type_sig c)
      end.

Axiom IO_unit : Set.
Axiom _IO : Set -> Set.
Axiom _IO_bind : forall {A B}, _IO A -> (A -> _IO B) -> _IO B.
Axiom _IO_return : forall {A : Set}, A -> _IO A.
Axiom cast_io : _IO unit -> IO_unit.
Extract Constant _IO "a" => "GHC.Base.IO a".
Extract Inlined Constant _IO_bind => "(Prelude.>>=)".
Extract Inlined Constant _IO_return => "GHC.Base.return".
Extract Inlined Constant IO_unit => "GHC.Base.IO ()".
Extract Inlined Constant cast_io => "".

Definition main : IO_unit
  := cast_io (_IO_bind (_IO_return output)
                       (fun _ => _IO_return tt)).

Recursive Extraction main.
