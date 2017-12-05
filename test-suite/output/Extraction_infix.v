(* @herbelin's example for issue #6212 *)

Require Import Extraction.
Inductive I := C : bool -> bool -> I.
Definition test := C true false.

(* the parentheses around the function wrong signalled an infix operator *)

Extract Inductive I => "foo" [ "(fun (b, p) -> bar)" ].
Extraction test.

(* some bonafide infix operators *)

Extract Inductive I => "foo" [ "(@@?)" ].
Extraction test.

Extract Inductive I => "foo" [ "(#^^)" ].
Extraction test.

Extract Inductive I => "foo" [ "(@?:::)" ].
Extraction test.

(* allow whitespace around infix operator *)

Extract Inductive I => "foo" [ "(  @?:::  )" ].
Extraction test.
