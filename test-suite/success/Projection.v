Structure S : Type := 
 {Dom     : Type;
  Op      : Dom -> Dom -> Dom}.

Check [s:S](Dom s).
Check [s:S](Op s).
Check [s:S;a,b:(Dom s)](Op s a b).

(* v8
Check fun s:S => s.(Dom).
Check fun s:S => s.(Op).
Check fun (s:S) (a b:s.(Dom)) => s.(Op) a b.
*)

Set Implicit Arguments.
Unset Strict Implicits. 

Structure S' [A:Set] : Type := 
 {Dom'     : Type;
  Op'      : A -> Dom' -> Dom'}.

Check [s:(S' nat)](Dom' s).
Check [s:(S' nat)](Op' 2!s).
Check [s:(S' nat)](!Op' nat s).
Check [s:(S' nat);a:nat;b:(Dom' s)](Op' a b).
Check [s:(S' nat);a:nat;b:(Dom' s)](!Op' nat s a b).

(* v8
Check fun s:S' => s.(Dom').
Check fun s:S' => s.(Op').
Check fun (s:S') (a b:s.(Dom')) => _.(Op') a b.
Check fun (s:S') (a b:s.(Dom')) => s.(Op') a b.

Set Implicit Arguments.
Unset Strict Implicits. 

Structure S' (A:Set) : Type := 
 {Dom'     : Type;
  Op'      : A -> Dom' -> Dom'}.

Check fun s:S' nat => s.(Dom').
Check fun s:S' nat => s.(Op').
Check fun (s:S' nat) (a:nat) (b:s.(Dom')) => _.(@Op' nat) a b.
Check fun (s:S' nat) (a:nat) (b:s.(Dom')) => s.(Op') a b.
*)
