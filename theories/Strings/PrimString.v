Require Import PrimInt63.

Definition char63 := int.

Primitive string := #string_type.

Primitive max_length : int := #string_max_length.

Primitive make : int -> char63 -> string := #string_make.

Primitive length : string -> int := #string_length.

Primitive get : string -> int -> char63 := #string_get.

Primitive sub : string -> int -> int -> string := #string_sub.

Primitive cat : string -> string -> string := #string_cat.

Primitive compare : string -> string -> comparison := #string_compare.

Module Export PStringNotations.
  Record string_wrapper := wrap_string {string_wrap : string}.
  Definition id_string (s : string) : string := s.
  Register string as strings.pstring.type.
  Register string_wrapper as strings.pstring.string_wrapper.
  Register wrap_string as strings.pstring.wrap_string.

  Declare Scope pstring_scope.
  Delimit Scope pstring_scope with pstring.
  Bind Scope pstring_scope with string.
  String Notation string id_string id_string : pstring_scope.
End PStringNotations.

Record char63_wrapper := wrap_char63 { char63_wrap : char63 }.

Module Export Char63Notations.
  Coercion char63_wrap : char63_wrapper >-> char63.
  Definition parse (s : string) : option char63_wrapper :=
    if PrimInt63.eqb (length s) 1%uint63 then Some (wrap_char63 (get s 0)) else None.
  Definition print (i : char63_wrapper) : option string :=
    if PrimInt63.ltb i.(char63_wrap) 256%uint63 then Some (make 1 i.(char63_wrap)) else None.

  Declare Scope char63_scope.
  Delimit Scope char63_scope with char63.
  Bind Scope char63_scope with char63.
  String Notation char63_wrapper parse print : char63_scope.
End Char63Notations.
