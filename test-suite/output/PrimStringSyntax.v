Require Import Uint63.
Require Import PrimString.

Check "hello"%pstring.
Check ""%pstring.

Check "a"%char63.
Check ("a"%char63 : char63).
Check 0%uint63.
Check (0%uint63 : char63).

Open Scope pstring.

Check "hello".
