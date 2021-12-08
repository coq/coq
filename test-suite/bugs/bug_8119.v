Require Import Coq.Strings.String.

Section T.
  Eval vm_compute in let x := tt in _.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
  Eval vm_compute in let _ := Set in _.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
  Eval vm_compute in let _ := Prop in _.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
End T.

Section U0.
  Let n : unit := tt.
  Eval vm_compute in _.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
  Goal exists tt : unit, tt = tt. eexists. vm_compute. Abort.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
End U0.

Section S0.
  Let LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
  Eval vm_compute in _.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
  Goal exists tt : unit, tt = tt. eexists. vm_compute. Abort.
(* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
End S0.

Class T := { }.
Section S1.
  Context {p : T}.
  Let LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
  Eval vm_compute in _.
(* Error: Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/. *)
  Goal exists tt : unit, tt = tt. eexists. vm_compute. Abort.
(* Error: Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/. *)
End S1.

Class M := { m : Type }.
Section S2.
  Context {p : M}.
  Let LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
  Eval vm_compute in _.
(* Error: Anomaly "File "pretyping/vnorm.ml", line 60, characters 9-15: Assertion failed." *)
  Goal exists tt : unit, tt = tt. eexists. vm_compute. Abort.
(* Error: Anomaly "File "pretyping/vnorm.ml", line 60, characters 9-15: Assertion failed." *)
End S2.
