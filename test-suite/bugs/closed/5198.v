(* -*- mode: coq; coq-prog-args: ("-boot" "-nois") -*- *)
(* File reduced by coq-bug-finder from original input, then from 286 lines to 
27 lines, then from 224 lines to 53 lines, then from 218 lines to 56 lines, 
then from 269 lines to 180 lines, then from 132 lines to 48 lines, then from 
253 lines to 65 lines, then from 79 lines to 65 lines *)
(* coqc version 8.6.0 (November 2016) compiled on Nov 12 2016 14:43:52 with 
OCaml 4.02.3
   coqtop version jgross-Leopard-WS:/home/jgross/Downloads/coq/coq-v8.6,v8.6 
(7e992fa784ee6fa48af8a2e461385c094985587d) *)
Axiom admit : forall {T}, T.
Set Printing Implicit.
Inductive nat := O | S (_ : nat).
Axiom f : forall (_ _ : nat), nat.
Class ZLikeOps (e : nat)
  := { LargeT : Type ; SmallT : Type ; CarryAdd : forall (_ _ : LargeT), LargeT 
}.
Class BarrettParameters :=
  { b : nat ; k : nat ; ops : ZLikeOps (f b k) }.
Axiom barrett_reduce_function_bundled : forall {params : BarrettParameters}
                                               (_ : @LargeT _ (@ops params)),
    @SmallT _ (@ops params).

Global Instance ZZLikeOps e : ZLikeOps (f (S O) e)
  := { LargeT := nat ; SmallT := nat ; CarryAdd x y := y }.
Definition SRep := nat.
Local Instance x86_25519_Barrett : BarrettParameters
  := { b := S O ; k := O ; ops := ZZLikeOps O }.
Definition SRepAdd : forall (_ _ : SRep), SRep
  := let v := (fun x y => barrett_reduce_function_bundled (CarryAdd x y)) in
     v.
Definition SRepAdd' : forall (_ _ : SRep), SRep
  := (fun x y => barrett_reduce_function_bundled (CarryAdd x y)).
(* Error:
In environment
x : SRep
y : SRep
The term "x" has type "SRep" while it is expected to have type
 "@LargeT ?e ?ZLikeOps".
 *)
