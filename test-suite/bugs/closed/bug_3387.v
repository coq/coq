Unset Strict Universe Declaration.
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
  let x := constr:(Type) in
  let y := constr:(Obj set_cat) in
  first [ unify x y | fail 2 "no unify" ];
    change x with y at -1. (* Error: Not convertible. *)
  reflexivity.
Defined.
