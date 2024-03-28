Require Import Ltac2.Ltac2.

Module AbstractType.
  (* redundant, maybe should be an error? *)
  #[abstract] Ltac2 Type t.
End AbstractType.

Module DefinedType.
  Module M.
    #[abstract] Ltac2 Type t := int.

    Ltac2 foo (x:t) : t := Int.add x 1.

    Ltac2 make (x:int) : t := x.
    Ltac2 repr (x:t) : int := x.

    Ltac2 three : t := 3.
  End M.

  Fail Ltac2 nope : M.t := 0.

  Ltac2 ok () : M.t := M.make 0.

  Ltac2 Eval ok ().

  Import M.

  Fail Ltac2 nope : M.t := 0.

  Ltac2 Eval repr (foo (make 1)).

  Print foo.
  Print three.

  Ltac2 Eval three.
End DefinedType.

Module AlgebraicType.
  Module M.
    #[abstract] Ltac2 Type t := [ A | B (int option) ].

    Ltac2 a := A.
    Ltac2 is_b x := match x with B _ => true | _ => false end.
    Ltac2 get_b def x := match x with B (Some x) => x | _ => def end.
  End M.

  Fail Ltac2 Eval M.A.

  Fail Ltac2 Eval fun x => match x with M.A => true | _ => false end.

  Ltac2 Eval M.a.

  Ltac2 Eval M.is_b M.a.

  Print M.a.
  Print M.is_b.
  Print M.get_b.
End AlgebraicType.

Module RecordType.
  Module M.
    #[abstract] Ltac2 Type 'a t := { mutable p : 'a }.

    Ltac2 make x := { p := x }.
    Ltac2 set x v := x.(p) := v.
    Ltac2 p x := x.(p).
  End M.

  Ltac2 Eval M.make 0.

  Import M.

  Fail Ltac2 Eval { p := 0 }.

  Fail Ltac2 Eval fun x => x.(p).

  Ltac2 Eval make 42.

  Ltac2 Eval p (make 42).

  Fail Ltac2 Eval Int.add (p (make true)) 0.

  Print make.
  Print p.
  Print set.
End RecordType.

Module ExtensibleType.
  Module M.
    (* TODO figure out what this should do, error until then. *)
    Fail #[abstract] Ltac2 Type t := [ .. ].

    (* Ltac2 Type t ::= [ E | E' ]. *)

    (* Fail #[abstract] Ltac2 Type t ::= [ F ]. *)

    (* Ltac2 e := E. *)

    (* Ltac2 is_e x := match x with E => true | _ => false end. *)
  End M.

  (* Import M. *)
  (* Ltac2 Eval E. *)

  (* Ltac2 Eval match E with E => true | _ => false end. *)

  (* Fail Ltac2 Type t ::= [ F ]. *)

  (* add more tests once we have something to test *)
End ExtensibleType.
