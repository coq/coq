
(* Refine and let-in's *)

Goal exists x : nat, x = 0.
 refine (let y := 0 + 0 in _).
exists y; auto.
Save test1.

Goal exists x : nat, x = 0.
 refine (let y := 0 + 0 in ex_intro _ (y + y) _).  
auto.
Save test2.

Goal nat.
 refine (let y := 0 in 0 + _).
exact 1.
Save test3.

(* Example submitted by Yves on coqdev *)

Require Import List.

Goal forall l : list nat, l = l.
Proof.
 refine
 (fun l =>
  match l return (l = l) with
  | nil => _
  | O :: l0 => _
  | S _ :: l0 => _
  end).
Abort.

(* Submitted by Roland Zumkeller (bug #888) *)

(* The Fix and CoFix rules expect a subgoal even for closed components of the
   (co-)fixpoint *)

Goal nat -> nat.
 refine (fix f (n : nat) : nat := S _
         with pred (n : nat) : nat := n
         for f).
exact 0.
Qed.

(* Submitted by Roland Zumkeller (bug #889) *)

(* The types of metas were in metamap and they were not updated when
   passing through a binder *)

Goal forall n : nat, nat -> n = 0.
 refine
 (fun n => fix f (i : nat) : n = 0 := match i with
                                      | O => _
                                      | S _ => _
                                      end).
Abort.

(* Submitted by Roland Zumkeller (bug #931) *)
(* Don't turn dependent evar into metas *)

Goal (forall n : nat, n = 0 -> Prop) -> Prop.
intro P.
 refine (P _ _).
reflexivity.
Abort.

(* Submitted by Jacek Chrzaszcz (bug #1102) *)

(* le probl�me a �t� r�solu ici par normalisation des evars pr�sentes
   dans les types d'evars, mais le probl�me reste a priori ouvert dans
   le cas plus g�n�ral d'evars non instanci�es dans les types d'autres
   evars *)

Goal exists n:nat, n=n.
refine (ex_intro _ _ _).
Abort.

(* Used to failed with error not clean *)

Definition div :
  forall x:nat, (forall y:nat, forall n:nat, {q:nat | y = q*n}) -> 
     forall n:nat, {q:nat | x = q*n}.
refine
  (fun m div_rec n =>
     match div_rec m n with
     | exist _ _ => _
     end).
Abort.


(* Use to fail because sigma was not propagated to get_type_of *)
(* Revealed by r9310, fixed in r9359 *)

Goal
  forall f : forall a (H:a=a), Prop,
 (forall a (H:a = a :> nat), f a H -> True /\ True) -> 
  True.
intros.
refine (@proj1 _ _ (H 0 _ _)).
Abort.

(* Use to fail because let-in with metas in the body where rejected
   because a priori considered as dependent *)

Require Import Peano_dec.

Definition fact_F : 
  forall (n:nat),
  (forall m, m<n -> nat) ->
  nat.
refine 
  (fun n fact_rec =>
     if eq_nat_dec n 0 then 
        1
     else
	let fn := fact_rec (n-1) _ in
        n * fn).
Abort.
