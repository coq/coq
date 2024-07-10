From Stdlib Require Import List.
From Stdlib.Strings Require Import String Byte Ascii.
Import ListNotations.

Set Printing Depth 100000.
Set Printing Width 1000.

Close Scope char_scope.
Close Scope string_scope.

Open Scope byte_scope.
Print byte_rect.
Print byte_rec.
Print byte_ind.
Check "000".
Check "a".
Check "127".
Fail Check "€".
Close Scope byte_scope.

Open Scope char_scope.
Check "000".
Check "a".
Check "127".
Fail Check "€".
Close Scope char_scope.

Open Scope string_scope.
Check "000".
Check "a".
Check "127".
Check "€".
Check String "001" EmptyString.
Close Scope string_scope.

Compute ascii_of_byte "a".
Compute byte_of_ascii "a".
Compute string_of_list_byte ("a"::nil)%byte.
Compute list_byte_of_string "a".

Local Open Scope byte_scope.
Compute List.fold_right
        (fun n ls => match Byte.of_nat n with
                     | Some b => cons b ls
                     | None => ls
                     end)
        nil
        (ListDef.seq 0 256).
Local Close Scope byte_scope.
Local Open Scope char_scope.
Compute List.map Ascii.ascii_of_nat (ListDef.seq 0 256).
Local Close Scope char_scope.

(* Test numeral notations for parameterized inductives *)
Module Test2.

Notation string := (list Byte.byte).
Definition id_string := @id string.

String Notation string id_string id_string : list_scope.

Check "abc"%list.

End Test2.

(* Test the via ... using ... option *)
Module Test3.

Inductive I :=
| IO : I
| IS : I -> I.

Definition of_byte (x : Byte.byte) : I :=
  let fix f n :=
      match n with
      | O => IO
      | S n => IS (f n)
      end in
  f (Byte.to_nat x).

Definition to_byte (x : I) : option Byte.byte :=
  let fix f i :=
      match i with
      | IO => O
      | IS i => S (f i)
      end in
  Byte.of_nat (f x).

String Notation nat of_byte to_byte (via I mapping [O => IO, S => IS]) : nat_scope.

Check "000".
Check "001".
Check "002".
Check "255".
Fail Check "256".

End Test3.

(* Test overlapping string notations *)
Module Test4.

Notation string1 := (list Byte.byte).
Definition id_string1 := @id string1.

String Notation string1 id_string1 id_string1 : list_scope.

Notation string2 := (list Ascii.ascii).
Definition a2b := List.map byte_of_ascii.
Definition b2a := List.map ascii_of_byte.

String Notation string2 b2a a2b : list_scope.

Check "abc"%list.
Check ["a";"b";"c"]%char%list : string2.
Check ["a";"b";"c"]%byte%list : string1.

End Test4.
