Set Universe Polymorphism.
Set Printing Universes.
Record Cat := { Obj :> Type }.
Definition set_cat := {| Obj := Type |}.
Goal Type@{i} = Type@{j}.
Proof.
  (* 1 subgoals
, subgoal 1 (ID 3)

  ============================
   Type@{Top.368} = Type@{Top.370}
(dependent evars:) *)
  let x := constr:(Type) in
  let y := constr:(Obj set_cat) in
  unify x y. (* success *)
  Fail let x := constr:(Type) in
  let y := constr:(Obj set_cat) in
  first [ unify x y | fail 2 "no unify" ];
    change x with y. (* Error: Not convertible. *)
