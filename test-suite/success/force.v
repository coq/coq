(* To run: [dune build theories/Force && dune exec -- dev/shim/coqc test.v] *)

Require Import Force.Force.

(**** UNIVERSES ****)

Definition check_run@{u1 u2} : forall (T : Type@{u1}) (K : Type@{u2}), Blocked T -> (T -> K) -> K := @run.
Definition check_Blocked@{u} : Type@{u} -> Type@{u} := Blocked.
Definition check_block@{u} : forall (T : Type@{u}), T -> Blocked@{u} T := @block.
Definition check_unblock@{u} : forall (T : Type@{u}), Blocked@{u} T -> T := @unblock.

(**** EVALUATION ****)

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation LAZY t := (ltac:(let x := eval lazy in t in exact x)) (only parsing).
Notation WHNF t := (ltac:(let x := eval lazywhnf  in t in exact x)) (only parsing).

Goal LAZY (@block) = @block.
Proof. syn_refl. Qed.

Goal WHNF (@block) = @block.
Proof. syn_refl. Qed.

Goal LAZY (@block nat) = @block nat.
Proof. syn_refl. Qed.

Goal WHNF (@block nat) = @block nat.
Proof. syn_refl. Qed.

Goal WHNF (@block (id nat)) = @block (id nat).
Proof. syn_refl. Qed.

Goal LAZY (@block (id nat)) = @block nat.
Proof. syn_refl. Qed.

Goal WHNF (block 0) = block 0.
Proof. syn_refl. Qed.

Goal LAZY (block 0) = block 0.
Proof. syn_refl. Qed.

Goal WHNF (block (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (block (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (id (block (0 + 0))) = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (id (block (0 + 0))) = block (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let x := 0 + 0 in block x))) = block 0.
Proof. syn_refl. Qed.

(* ... *)

Goal LAZY ((fun f => f (1 + 1)) block) = block 2.
Proof. syn_refl. Qed.

Goal LAZY ((fun f => f (1 + 1)) (fun x => block x)) = block 2.
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) block) = block (1+1).
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) (fun x => block x)) = block (1 + 1).
Proof. syn_refl. Qed.

Inductive True := I.
Definition id : True -> True := fun x => x.

Definition g := fun x:True => x.
Definition h := fun x:True => x.
Axiom and : True -> True -> True.
Axiom Pr : True -> Prop.

(* Non-lexical unblock is just a "projection" *)
Goal WHNF ((fun f => f (block (id I = id I))) unblock) = (id I = id I).
Proof. syn_refl. Qed.

(* Non-lexical run is just a "projection" *)
Goal WHNF ((fun f => f (block (id I = id I)) (fun x => x)) run) = (id I = id I).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let x := (and (g I) (h I)) in block x))) = (block (and I I)).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := (fun x : id I = I => True) in block x)) = (fun x : I = I => True).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := forall x : id I = I, True in block x)) = (forall x : I = I, True).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := id I in block (forall u:unit, x = x))) = (forall (u:unit), I = I).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := 1 + 1 in block x)) = 2.
Proof. syn_refl. Qed.

Goal WHNF (run (block (1+1)) (fun x => x)) = WHNF (match 1 + 1 with S x => S x | 0 => 0 end).
Proof. syn_refl. Qed.

Goal WHNF (block (run (let n := I in block n) (fun x : True => x)))
        = (block (run (let n := I in block n) (fun x : True => x))).
Proof. syn_refl. Qed.

Goal WHNF (block (run (let x := (fun x => x) tt in block x) (fun x => x)))
        = (block (run (let x := (fun x => x) tt in block x) (fun x => x))).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let x := (fun x => x) tt in block x))) = block tt.
Proof. syn_refl. Qed.

(*
block (unblock (let x := (fun x => x) tt in block x)) @ ε | ∅ --{whnf}-->
block @ (unblock (let x := (fun x => x) tt in block x)) . ε | ∅ --{whnf}-->

  unblock (let x := (fun x => x) tt in block x) @ ε | ∅ --{id}-->
  unblock @ (let x := (fun x => x) tt in block x) . ε | ∅ --{id}-->

    let x := (fun x => x) tt in block x @ ε | ∅ --{full}-->
    block x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{full}-->

      x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{id}-->

        (λ x => x) tt @ ε | ∅ --{full}-->
        λ x => x @ tt . ε | ∅ --{full}-->
        x @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

          tt @ ε | ∅ --{full}--> (value)

        tt @ ε | ∅[x{full} := <tt, ∅>] --{full}--> (value)

      tt @ ε | ∅[x{full} := <tt, ∅>] --{id}--> (value, updated closure)

    block tt @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

  unblock @ block tt . ε | ∅ --{id}-->
  tt @ ε | ∅ --{id}-->

block @ tt . ε | ∅ --{whnf}--> (done)
*)

Goal WHNF (block (run (let n := 2 + 2 in block n) (fun x : nat => 2 * 1)))
        = (block (run (let n := 2 + 2 in block n) (fun x : nat => 2 * 1))).
        (* = (block ((fun _ : nat => 2 * 1) 4)). *)
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block n) (2 + 2)) (fun x : nat => 2 * 1)))
        = (block (run ((fun n => block n) (2 + 2)) (fun x : nat => 2 * 1))).
        (* = (block ((fun _ : nat => 2 * 1) 4)). *)
Proof. syn_refl. Qed.

Inductive n := N | O.
Definition a (x y : n) :=
  match x with
  | N => y
  | O => O
  end.
Goal WHNF (block (unblock ((fun x => block (a x O)) (a N N)))) = block (a N O).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock ((fun x => block x) (a N N)))) = block (N).
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block (n + 1)) (2 + 2)) (fun x : nat => 2 * 1)))
        = (block (run ((fun n => block (n + 1)) (2 + 2)) (fun x : nat => 2 * 1))).
        (* = (block ((fun _ : nat => 2 * 1) (4 + 1))). *)
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let n := 0 + 0 in block (n + n))))
        = block (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let n := 0 + 0 in block (1 + unblock (let m := 0 + 0 in block (1 + m))))))
        = block (1 + (1 + 0)).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (
                      let n := 0 + 0 in
                      block (1 + n + unblock (
                                     let m := 2 + 2 in
                                     block (1 + m + unblock (
                                                        let k := 3 + 3 in
                                                        block (1 + n + m + k))))))))
        = block (1 + 0 + (1 + 4 + (1 + 0 + 4 + 6))).
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (block (2 + 2)) = block (2 + 2).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block 42)) = 42.
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (2 + 2))) = 4.
Proof. syn_refl. Qed.

Goal LAZY (unblock ((fun _ => block (2 + 2)) tt)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (block (fun x => (2 + 2) + x)) = block (fun x => (2 + 2) + x).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (fun x => (2 + 2) + x))) = fun x => S (S (S (S x))).
Proof. syn_refl. Qed.

Goal WHNF (run (let x := 1 + 1 in block (x + 1)) (fun x => forall y, y = x))
        = forall y, y = 2 + 1.
Proof. syn_refl. Qed.

Set Printing Width 1000.
Section AllArgs.
  Context (b : Blocked (nat -> nat)).

  Goal LAZY (unblock b 0) = unblock b 0.
  Proof. syn_refl. Qed.

  Goal WHNF (unblock b 0) = unblock b 0.
  Proof. syn_refl. Qed.

  Goal LAZY (run b (fun x n => n) 0) = run b (fun x n => n) 0.
  Proof. syn_refl. Qed.

  Goal WHNF (run b (fun x n => n) 0) = run b (fun x n => n) 0.
  Proof. syn_refl. Qed.
End AllArgs.

Goal LAZY (unblock (block (fun x => block x)) (0 + 0)) = block (0).
Proof. syn_refl. Qed.

Goal WHNF (unblock (block (fun x => block x)) (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (run (block (fun x => block x)) (fun f x => f x) (0 + 0)) = block (0).
Proof. syn_refl. Qed.

Goal WHNF (run (block (fun x => block x)) (fun f x => f x) (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Axiom F : run (let x := id I in block (id x)) (fun x => forall y, y = x).
Goal I=I.
  Succeed refine (F I).
  Succeed apply (F I).
  Succeed eapply (F I).
  Succeed exact (F I).
  Succeed eexact (F I).
  exact (F I).
Qed.

Module FunctionTypes.
  (* The example below should not call reduction on [id id R] _at all_! *)
  Inductive D := | d.
  Inductive R := | r (b: D).
  Definition id (x:Set) := x.
  Eval lazywhnf in @unblock R (let f := (fun x : id (id R) => block x) in @block R (@unblock R (f (r d)))).
End FunctionTypes.

Module Conversion.
  Axiom not : Prop -> Prop.
  Axiom TODO: forall {A:Prop}, A.

  Lemma test p :
    (forall _ : True, @unblock Prop (block (not p))).
    exact (@TODO (forall _ : True, not p)).
  Qed.
End Conversion.

Module Bla.
  Inductive prop :=.
  Axiom TODO: forall {A}, A.
  Definition reflect (p:prop) : Blocked Prop := match p with end.
  Lemma simplify_ok (p : prop) : False <-> unblock (reflect p).
  Proof.
    lazy.                       (* Used to fail *)
    destruct p.
  Qed.
End Bla.
