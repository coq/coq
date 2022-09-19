Require Import Ltac2.Ltac2.
Ltac2 foo () := let v := Constr.Unsafe.make (Constr.Unsafe.Rel -1) in
                let x := Constr.Binder.make None 'True in
                let vv := Constr.Unsafe.make (Constr.Unsafe.App v (Array.of_list [v])) in
                let f := Constr.Unsafe.make (Constr.Unsafe.Lambda x vv) in
                let ff := Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list [f])) in
                Std.eval_hnf ff.
Set Ltac2 Backtrace.
Ltac2 Eval foo ().
(* Error: Anomaly "Uncaught exception Not_found."
Please report at http://coq.inria.fr/bugs/.
*)
