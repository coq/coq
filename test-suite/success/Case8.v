(* Check dependencies in the matching predicate (was failing in V8.0pl1) *)

Inductive t : (x:O=O) x=x -> Prop := 
  c : (x:0=0) (t x (refl_equal ? x)).

Definition a [x:(t ? (refl_equal ? (refl_equal ? O)))] :=
  <[_;_;x]Cases x of (c y) => Prop end>Cases x of (c y) => y=y end.
