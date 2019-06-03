let simple_check1 env sigma evalue =
(* This version should be preferred if you want to really
  verify that the input is well-typed,
  and if you want to obtain the type. *)
(* Note that the output value is a pair containing a new evar_map:
   typing will fill out blanks in the term by add evar bindings. *)
  Typing.type_of env sigma evalue

let simple_check2 env sigma evalue =
(* This version should be preferred if you already expect the input to
  have been type-checked before.  Set ~lax to false if you want an anomaly
  to be raised in case of a type error.  Otherwise a ReTypeError exception
  is raised. *)
  Retyping.get_type_of ~lax:true env sigma evalue
