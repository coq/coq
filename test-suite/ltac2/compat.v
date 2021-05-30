Require Import Ltac2.Ltac2.

Import Ltac2.Notations.

(** Test calls to Ltac1 from Ltac2 *)

Ltac2 foo () := ltac1:(discriminate).

Goal true = false -> False.
Proof.
foo ().
Qed.

Goal true = false -> false = true.
Proof.
intros H; ltac1:(match goal with [ H : ?P |- _ ] => rewrite H end); reflexivity.
Qed.

Goal true = false -> false = true.
Proof.
intros H; ltac1:(rewrite H); reflexivity.
Abort.

(** Variables do not cross the compatibility layer boundary. *)
Fail Ltac2 bar nay := ltac1:(discriminate nay).

Fail Ltac2 pose1 (v : constr) :=
  ltac1:(pose $v).

(** Variables explicitly crossing the boundary must satisfy typing properties *)
Goal True.
Proof.
(* Wrong type *)
Fail ltac1:(x |- idtac) 0.
(* OK, and runtime has access to variable *)
ltac1:(x |- idtac x) (Ltac1.of_constr constr:(Type)).

(* Same for ltac1val *)
Fail Ltac1.run (ltac1val:(x |- idtac) 0).
Ltac1.run (ltac1val:(x |- idtac x) (Ltac1.of_constr constr:(Type))).
Abort.

(** Check value-returning FFI *)

(* A dummy CPS wrapper in Ltac1 *)
Ltac arg k :=
match goal with
| [ |- ?P ] => k P
end.

Ltac2 testeval v :=
  let r := { contents := None } in
  let k c :=
    let () := match Ltac1.to_constr c with
    | None => ()
    | Some c => r.(contents) := Some c
    end in
    (* dummy return value *)
    ltac1val:(idtac)
  in
  let tac := ltac1val:(arg) in
  let () := Ltac1.apply tac [Ltac1.lambda k] (fun _ => ()) in
  match r.(contents) with
  | None => fail
  | Some c => if Constr.equal v c then () else fail
  end.

Goal True.
Proof.
testeval 'True.
Abort.

Goal nat.
Proof.
testeval 'nat.
Abort.

(* CPS towers *)
Ltac2 testeval2 tac :=
  let fail _ := Control.zero Not_found in
  let cast c := match Ltac1.to_constr c with
  | None => fail ()
  | Some c => c
  end in
  let f x y z :=
    let x := cast x in
    let y := cast y in
    let z := cast z in
    Ltac1.of_constr constr:($x $y $z)
  in
  let f := Ltac1.lambda (fun x => Ltac1.lambda (fun y => Ltac1.lambda (fun z => f x y z))) in
  Ltac1.apply tac [f] Ltac1.run.

Goal False -> True.
Proof.
ltac1:(
let ff := ltac2:(tac |- testeval2 tac) in
ff ltac:(fun k =>
  let c := k (fun (n : nat) (i : True) (e : False) => i) O I in
  exact c)
).
Qed.

(** Test calls to Ltac2 from Ltac1 *)

Set Default Proof Mode "Classic".

Ltac foo := ltac2:(foo ()).

Goal true = false -> False.
Proof.
ltac2:(foo ()).
Qed.

Goal true = false -> False.
Proof.
foo.
Qed.

(** Variables do not cross the compatibility layer boundary. *)
Fail Ltac bar x := ltac2:(foo x).

Ltac mytac tac := idtac "wow".

Goal True.
Proof.
(** Fails because quotation is evaluated eagerly *)
Fail mytac ltac2:(fail).
(** One has to thunk thanks to the idtac trick *)
let t := idtac; ltac2:(fail) in mytac t.
constructor.
Qed.
