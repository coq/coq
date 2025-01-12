Require PrimString.

Declare Scope t_scope.
Delimit Scope t_scope with ts.

Import PrimString.
Inductive t := v : string -> t.
Definition parse : string -> t := v.
Definition print : t -> string := fun x => match x with v s => s end.
String Notation t parse print : t_scope.
Check v "bla".                (* string notation not used: [v "bla"] *)
