(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)

Require Import ssreflect.
Require Import ssrbool ssrfun TestSuite.ssr_mini_mathcomp.
Axiom daemon : False. Ltac myadmit := case: daemon.

(* Ltac debugging feature: recursive elim + eq generation *)
Lemma testL1 : forall A (s : seq A), s = s.
Proof.
move=> A s; elim branch: s => [|x xs _].
match goal with _ : _ = [::] |- [::] = [::] => move: branch => // | _ => fail end.
match goal with _ : _ =  _ :: _ |- _ :: _ = _ :: _ => move: branch => // | _ => fail end.
Qed.

(* The same but with explicit eliminator and a conflict in the intro pattern *)
Lemma testL2 : forall A (s : seq A), s = s.
Proof.
move=> A s; elim/last_ind branch: s => [|x s _].
match goal with _ : _ = [::] |- [::] = [::] => move: branch => // | _ => fail end.
match goal with _ : _ =  rcons _ _ |- rcons _ _ = rcons _ _ => move: branch => // | _ => fail end.
Qed.

(* The same but without names for variables involved in the generated eq *)
Lemma testL3 : forall A (s : seq A), s = s.
Proof.
move=> A s; elim branch: s; move: (s) => _.
match goal with _ : _ = [::] |- [::] = [::] => move: branch => // | _ => fail end.
move=> _; match goal with _ : _ =  _ :: _ |- _ :: _ = _ :: _ => move: branch => // | _ => fail end.
Qed.

Inductive foo : Type := K1 : foo | K2 : foo -> foo -> foo | K3 : (nat -> foo) -> foo.

(* The same but with more intros to be done *)
Lemma testL4 : forall (o : foo), o = o.
Proof.
move=> o; elim branch: o.
match goal with _ : _ = K1 |- K1 = K1 => move: branch => // | _ => fail end.
move=> _; match goal with _ : _ = K2 _ _ |- K2 _ _ = K2 _ _ => move: branch => // | _ => fail end.
move=> _; match goal with _ : _ =  K3 _ |- K3 _ = K3 _ => move: branch => // | _ => fail end.
Qed.

(* Occurrence counting *)
Lemma testO1: forall (b : bool), b = b.
Proof.
move=> b; case: (b) / idP.
match goal with |- is_true b -> true = true => done | _ => fail end.
match goal with |- ~ is_true b -> false = false => done | _ => fail end.
Qed.

(* The same but only the second occ *)
Lemma testO2: forall (b : bool), b = b.
Proof.
move=> b; case: {2}(b) / idP.
match goal with |- is_true b -> b = true => done | _ => fail end.
match goal with |- ~ is_true b -> b = false => move/(introF idP) => // | _ => fail end.
Qed.

(* The same but with eq generation *)
Lemma testO3: forall (b : bool), b = b.
Proof.
move=> b; case E: {2}(b) / idP.
match goal with _ : is_true b, _ : b = true |- b = true => move: E => _; done | _ => fail end.
match goal with H : ~ is_true b, _ : b = false |- b = false => move: E => _; move/(introF idP): H => // | _ => fail end.
Qed.

(* Views *)
Lemma testV1 : forall A (s : seq A), s = s.
Proof.
move=> A s; case/lastP E: {1}s => [| x xs].
match goal with _ : s = [::] |- [::] = s => symmetry; exact E | _ => fail end.
match goal with _ : s = rcons x xs |- rcons _ _ = s => symmetry; exact E | _ => fail end.
Qed.

Lemma testV2 : forall A (s : seq A), s = s.
Proof.
move=> A s; case/lastP E: s => [| x xs].
match goal with _ : s = [::] |- [::] = [::] => done | _ => fail end.
match goal with _ : s = rcons x xs |- rcons _ _ = rcons _ _ => done | _ => fail end.
Qed.

Lemma testV3 : forall A (s : seq A), s = s.
Proof.
move=> A s; case/lastP: s => [| x xs].
match goal with |- [::] = [::] => done | _ => fail end.
match goal with |- rcons _ _ = rcons _ _ => done | _ => fail end.
Qed.

(* Patterns *)
Lemma testP1: forall (x y : nat), (y == x) && (y == x) -> y == x.
move=> x y; elim: {2}(_ == _) / eqP.
match goal with |- (y = x -> is_true ((y == x) && true) -> is_true (y == x)) => move=> -> // | _ => fail end.
match goal with |- (y <> x -> is_true ((y == x) && false) -> is_true (y == x)) => move=> _; rewrite andbC // | _ => fail end.
Qed.

(* The same but with an implicit pattern *)
Lemma testP2 : forall (x y : nat), (y == x) && (y == x) -> y == x.
move=> x y; elim: {2}_ / eqP.
match goal with |- (y = x -> is_true ((y == x) && true) -> is_true (y == x)) => move=> -> // | _ => fail end.
match goal with |- (y <> x -> is_true ((y == x) && false) -> is_true (y == x)) => move=> _; rewrite andbC // | _ => fail end.
Qed.

(* The same but with an eq generation switch *)
Lemma testP3 : forall (x y : nat), (y == x) && (y == x) -> y == x.
move=> x y; elim E: {2}_ / eqP.
match goal with _ : y = x |- (is_true ((y == x) && true) -> is_true (y == x)) => rewrite E; reflexivity | _ => fail end.
match goal with _ : y <> x |- (is_true ((y == x) && false) -> is_true (y == x)) => rewrite E => /= H; exact H  | _ => fail end.
Qed.

Inductive spec : nat -> nat -> nat -> Prop :=
| specK : forall a b c, a = 0 -> b = 2 -> c = 4 -> spec a b c.
Lemma specP : spec 0 2 4. Proof. by constructor. Qed.

Lemma testP4 : (1+1) * 4 = 2 + (1+1) + (2 + 2).
Proof.
case: specP => a b c defa defb defc.
match goal with |- (a.+1 + a.+1) * c = b + (a.+1 + a.+1) + (b + b) => subst; done | _ => fail end.
Qed.

Lemma testP5 : (1+1) * 4 = 2 + (1+1) + (2 + 2).
Proof.
case: (1 + 1) _ / specP => a b c defa defb defc.
match goal with |- b * c = a.+2 + b + (a.+2 + a.+2) => subst; done | _ => fail end.
Qed.

Lemma testP6 : (1+1) * 4 = 2 + (1+1) + (2 + 2).
Proof.
case: {2}(1 + 1) _ / specP => a b c defa defb defc.
match goal with |- (a.+1 + a.+1) * c = a.+2 + b + (a.+2 + a.+2) => subst; done | _ => fail end.
Qed.

Lemma testP7 : (1+1) * 4 = 2 + (1+1) + (2 + 2).
Proof.
case: _ (1 + 1) (2 + _) / specP => a b c defa defb defc.
match goal with |- b * a.+4 = c + c => subst; done | _ => fail end.
Qed.

Lemma testP8 : (1+1) * 4 = 2 + (1+1) + (2 + 2).
Proof.
case E: (1 + 1) (2 + _) / specP=> [a b c defa defb defc].
match goal with |- b * a.+4 = c + c => subst; done | _ => fail end.
Qed.

Variables (T : Type) (tr : T -> T).

Inductive exec (cf0 cf1 : T) : seq T -> Prop :=
| exec_step : tr cf0 = cf1 -> exec cf0 cf1 [::]
| exec_star : forall cf2 t, tr cf0 = cf2 ->
  exec cf2 cf1 t -> exec cf0 cf1 (cf2 :: t).

Inductive execr (cf0 cf1 : T) : seq T -> Prop :=
| execr_step : tr cf0 = cf1 -> execr cf0 cf1 [::]
| execr_star : forall cf2 t, execr cf0 cf2 t ->
  tr cf2 = cf1 -> execr cf0 cf1 (t ++ [:: cf2]).

Lemma execP : forall cf0 cf1 t, exec cf0 cf1 t <-> execr cf0 cf1 t.
Proof.
move=> cf0 cf1 t; split => [] Ecf.
  elim: Ecf.
    match goal with |- forall cf2 cf3 : T, tr cf2 = cf3 ->
      execr cf2 cf3 [::] => myadmit | _ => fail end.
  match goal with |- forall (cf2 cf3 cf4 : T) (t0 : seq T),
   tr cf2 = cf4 -> exec cf4 cf3 t0 -> execr cf4 cf3 t0 ->
   execr cf2 cf3 (cf4 :: t0) => myadmit | _ => fail end.
elim: Ecf.
  match goal with |- forall cf2 : T,
    tr cf0 = cf2 -> exec cf0 cf2 [::] => myadmit | _ => fail end.
match goal with |- forall (cf2 cf3 : T) (t0 : seq T),
 execr cf0 cf3 t0 -> exec cf0 cf3 t0 -> tr cf3 = cf2 ->
 exec cf0 cf2 (t0 ++ [:: cf3]) => myadmit | _ => fail end.
Qed.

Fixpoint plus (m n : nat) {struct n} : nat :=
   match n with
   | 0 => m
   | S p => S (plus m p)
   end.

Definition plus_equation :
forall m n : nat,
       plus m n =
       match n with
       | 0 => m
       | p.+1 => (plus m p).+1
       end
:=
fun m n : nat =>
match
  n as n0
  return
    (forall m0 : nat,
     plus m0 n0 =
     match n0 with
     | 0 => m0
     | p.+1 => (plus m0 p).+1
     end)
with
| 0 => @erefl nat
| n0.+1 => fun m0 : nat => erefl (plus m0 n0).+1
end m.

Definition plus_rect :
forall (m : nat) (P : nat -> nat -> Type),
       (forall n : nat, n = 0 -> P 0 m) ->
       (forall n p : nat,
        n = p.+1 -> P p (plus m p) -> P p.+1 (plus m p).+1) ->
       forall n : nat, P n (plus m n)
:=
fun (m : nat) (P : nat -> nat -> Type)
  (f0 : forall n : nat, n = 0 -> P 0 m)
  (f : forall n p : nat,
       n = p.+1 -> P p (plus m p) -> P p.+1 (plus m p).+1) =>
fix plus0 (n : nat) : P n (plus m n) :=
  eq_rect_r [eta P n]
    (let f1 := f0 n in
     let f2 := f n in
     match
       n as n0
       return
         (n = n0 ->
          (forall p : nat,
           n0 = p.+1 -> P p (plus m p) -> P p.+1 (plus m p).+1) ->
          (n0 = 0 -> P 0 m) ->
          P n0 match n0 with
               | 0 => m
               | p.+1 => (plus m p).+1
               end)
     with
     | 0 =>
         fun (_ : n = 0)
           (_ : forall p : nat,
                0 = p.+1 ->
                P p (plus m p) -> P p.+1 (plus m p).+1)
           (f4 : 0 = 0 -> P 0 m) => unkeyed (f4 (erefl 0))
     | n0.+1 =>
         fun (_ : n = n0.+1)
           (f3 : forall p : nat,
                 n0.+1 = p.+1 ->
                 P p (plus m p) -> P p.+1 (plus m p).+1)
           (_ : n0.+1 = 0 -> P 0 m) =>
         let f5 :=
           let p := n0 in
           let H := erefl n0.+1 : n0.+1 = p.+1 in f3 p H in
         unkeyed (let Hrec := plus0 n0 in f5 Hrec)
     end (erefl n) f2 f1) (plus_equation m n).

Definition plus_ind := plus_rect.

Lemma exF x y z: plus (plus x y) z = plus x (plus y z).
elim/plus_ind: z / (plus _ z).
match goal with |- forall n : nat, n = 0 -> plus x y = plus x (plus y 0) => idtac end.
Undo 2.
elim/plus_ind: (plus _ z).
match goal with |- forall n : nat, n = 0 -> plus x y = plus x (plus y 0) => idtac end.
Undo 2.
elim/plus_ind: {z}(plus _ z).
match goal with |- forall n : nat, n = 0 -> plus x y = plus x (plus y 0) => idtac end.
Undo 2.
elim/plus_ind: {z}_.
match goal with |- forall n : nat, n = 0 -> plus x y = plus x (plus y 0) => idtac end.
Undo 2.
elim/plus_ind: z / _.
match goal with |- forall n : nat, n = 0 -> plus x y = plus x (plus y 0) => idtac end.
 done.
by move=> _ p _ ->.
Qed.

(* BUG elim-False *)
Lemma testeF : False -> 1 = 0.
Proof. by elim. Qed.
