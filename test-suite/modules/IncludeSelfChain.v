(* Include-self subtyping checks for chains of functor module types
   (see rocq-prover/rocq#22279).

   Each [<+] of a functor module type instantiates the functor's parameter
   with the module type under construction, which triggers a subtyping
   check of the accumulated signature against the parameter's signature.
   These tests exercise that path with empty and non-empty parameter
   signatures, definitions (checked up to conversion), inductive types,
   submodules, and prefix-shaped chains where the same fields are
   re-checked at every stage. *)

(* Chains over an empty parameter signature *)

Module Type EmptyArgs. End EmptyArgs.
Module Type E1 (Import args : EmptyArgs). Parameter e1 : Type. End E1.
Module Type E2 (Import args : EmptyArgs). Parameter e2 : Type. End E2.
Module Type E3 (Import args : EmptyArgs). Parameter e3 : Type. End E3.

Module Type EChain := E1 <+ E2 <+ E3.

(* Chains over a shared parameter signature with a couple of fields,
   including fields referring to each other and a definition *)

Module Type Args.
  Parameter t : Type.
  Parameter op : t -> t.
  Parameter e : t.
  Definition twice (x : t) : t := op (op x).
End Args.

Module Type I1 (Import args : Args).
  Parameter f1 : t -> t.
End I1.
Module Type I2 (Import args : Args).
  Parameter f2 : twice e = twice e.
End I2.

Module Type Chain := Args <+ I1 <+ I2.

(* The definition [twice] in the accumulated signature is checked, up to
   conversion, against the definition expected by each parameter. *)

Module Type ArgsEta.
  Parameter t : Type.
  Parameter op : t -> t.
  Parameter e : t.
  Definition twice : t -> t := fun x => op (op x).
End ArgsEta.

Module Type I3 (Import args : ArgsEta).
  Parameter f3 : t.
End I3.

Module Type ChainEta := Args <+ I3.

(* A parameter cannot implement an expected definition *)

Module Type ArgsDef.
  Definition d : nat := 0.
End ArgsDef.
Module Type UsesDef (Import args : ArgsDef).
  Parameter u : d = 0.
End UsesDef.

Module Type BadArgsDef.
  Parameter d : nat.
End BadArgsDef.

Fail Module Type BadDefChain := BadArgsDef <+ UsesDef.
Module Type GoodDefChain := ArgsDef <+ UsesDef.

(* Type mismatches are still detected *)

Module Type BadArgs.
  Parameter t : Type.
  Parameter op : t.
  Parameter e : t.
  Definition twice (x : t) : t := x.
End BadArgs.

Fail Module Type BadChain := BadArgs <+ I1.

(* Inductive types and submodules in the parameter signature *)

Module Type ArgsInd.
  Inductive w : Set := A : w.
  Module Sub.
    Definition x : nat := 0.
  End Sub.
End ArgsInd.

Module Type I4 (Import args : ArgsInd).
  Parameter f4 : w -> w.
End I4.

Module Type ChainInd := ArgsInd <+ I4.

(* Prefix-shaped chains: stage [k] is parameterized by the whole chain up
   to stage [k-1], so the same fields are re-checked at every stage. *)

Module Type P0. Parameter t0 : Type. End P0.
Module Type A0 := P0.
Module Type P1 (Import a : A0). Parameter t1 : Type. End P1.
Module Type A1 := A0 <+ P1.
Module Type P2 (Import a : A1). Parameter t2 : Type. End P2.
Module Type A2 := A1 <+ P2.
Module Type P3 (Import a : A2). Parameter t3 : Type. End P3.
Module Type A3 := A2 <+ P3.
Module Type P4 (Import a : A3). Parameter t4 : Type. End P4.
Module Type A4 := A3 <+ P4.

(* Functors applied to modules keep checking their argument *)

Module Type Sig.
  Parameter t : Type.
  Parameter e : t.
End Sig.

Module M.
  Definition t : Type := nat.
  Definition e : t := 0.
End M.

Module F (X : Sig).
  Definition v := X.e.
End F.

Module App1 := F M.
Module App2 := F M.
Module App3 := F M.

Module BadM.
  Definition t : Type := nat.
  Definition e : bool := true.
End BadM.

Fail Module BadApp := F BadM.

(* Includes of applied functors whose argument is a functor parameter *)

Module G (X : Args).
  Include I1 X.
End G.

(* Rolling back and redoing a check must reproduce its universe
   constraints (cached subtyping verdicts are rolled back with the
   state they were computed in) *)

Set Warnings "-undo-batch-mode".
Module App4 := F M.
Reset App4.
Module App4 := F M.
