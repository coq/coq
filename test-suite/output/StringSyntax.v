Require Import Coq.Lists.List.
Require Import Coq.Strings.String Coq.Strings.Byte Coq.Strings.Ascii.
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
        (List.seq 0 256).
Local Close Scope byte_scope.
Local Open Scope char_scope.
Compute List.map Ascii.ascii_of_nat (List.seq 0 256).
Local Close Scope char_scope.
