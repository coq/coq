
Inductive sBool : SProp := strue | sfalse.

Set Definitional UIP.

Inductive seq {A:SProp} (a:A) : A -> SProp := srefl : seq a a.
Arguments srefl {_ _}, {_} _.

Definition x (b:bool) := if b then strue else sfalse.

Definition proof : seq (x true) (x false) := srefl.

Record Box (A:SProp) : Prop := box { unbox : A }.
Arguments box {_}.

Definition foo :=
  match proof return SProp with
  | srefl _ => nat -> seq x x
  end.

Eval lazy in foo.

Definition bla (f:foo) := f 0.
