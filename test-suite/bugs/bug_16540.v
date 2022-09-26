Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Import Constr.Unsafe.
Ltac2 mkApp (f : constr) (args : constr list) :=
  make (App f (Array.of_list args)).
Ltac2 mkVar (i : ident) :=
  make (Var i).
Goal True.
  let c := Constr.in_context @foo '_ (fun () => let term := mkApp (mkVar @foo) ['I] in
                                                printf "%t" term;
                                                Control.refine (fun () => term)) in
  ().
  (* Error: Anomaly "Uncaught exception Constr.DestKO." Please report at http://coq.inria.fr/bugs/. *)
Abort.
