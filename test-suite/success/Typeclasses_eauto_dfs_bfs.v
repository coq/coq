Class A := a : nat.
Class B := b : nat.
Class C := c : nat.
Class D := d : nat.

#[local] Instance CtoA : C -> A := fun x => x.
#[local] Instance BtoA : B -> A := fun x => x.
#[local] Instance DtoB : D -> B := fun x => x.

#[local] Instance someC : C := 2.
#[local] Instance someD : D := 3.

(** Here is our class structure: *)
(*
                A
              /   \
             B     C*
            /
           D*
*)

(** In a dfs (depth-first search) the instance at D* should be found. In a bfs (breadth-first search) the instance at C* should be found. *)

Set Typeclasses Debug.

(** We test that [typeclasses eauto] is really using bfs or dfs. *)

Goal exists x : A, x = 3.
simple notypeclasses refine (ex_intro _ _ _).
1: typeclasses eauto.
reflexivity.
Qed.

Goal exists x : A, x = 2.
simple notypeclasses refine (ex_intro _ _ _).
1: typeclasses eauto bfs.
reflexivity.
Qed.

Set Typeclasses Iterative Deepening.

Goal exists x : A, x = 3.
simple notypeclasses refine (ex_intro _ _ _).
1: typeclasses eauto dfs.
reflexivity.
Qed.

Goal exists x : A, x = 2.
simple notypeclasses refine (ex_intro _ _ _).
1: typeclasses eauto.
reflexivity.
Qed.
