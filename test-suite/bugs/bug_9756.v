
Module Bad.

Record box (A : Set) : Prop := Box { _ : A }.
Record foo@{i} (A:Type@{i}) := Foo { _ : Set:Type@{i} }.
Require Import TestSuite.hurkens.
Fail Definition bad : False := NoRetractFromSmallPropositionToProp.paradox
  _ _ (fun '(Foo _ x) => box x) (fun _ '(Box _ x) => x) Box _.
(* Error: Anomaly "Bad recursive type." Please report at http://coq.inria.fr/bugs/. *)

End Bad.

Module Alt.
  Inductive Box (A:Type) := box (_:A).

  (* it would be better if pattern matching compilation used template
     poly to make this succeed *)
  Fail Check (fun v => match v with box _ x => x end)
    :> forall x : (_ (* success if this is Box True *) :> Prop), True.
End Alt.
