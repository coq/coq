From Corelib Require Import Setoid Morphisms.

Axiom lattice_for : Type -> Type.
Axiom constant : forall {T : Type}, T -> lattice_for T.

Axiom lattice_for_rect :
forall [T : Type] (P : Type), (forall t : T, P) -> forall l : lattice_for T, P.

#[local]
Declare Instance lattice_for_rect_Proper_85 : forall {A},
  Proper (forall_relation (fun _ => eq) ==> eq ==> Basics.flip Basics.impl)
           (@lattice_for_rect A Prop) | 3.

Axiom lattice_rewrite :
  forall (A T T' : Type) (x : T -> T') (c : A -> lattice_for T)
      (v : lattice_for A),
    lattice_for_rect T' x (lattice_for_rect (lattice_for T) c v) =
    lattice_for_rect T' (fun x0 : A => lattice_for_rect T' x (c x0)) v.

Axiom collapse_might_be_empty : bool.

Axiom PosSet : Type.
Axiom PosSet_inter : PosSet -> PosSet -> PosSet.

Goal
forall
  (l2 : lattice_for PosSet)
  (l0 : lattice_for PosSet),
  lattice_for_rect Prop
    (fun x : PosSet =>
     lattice_for_rect Prop
       (fun _ : PosSet => True)
       (lattice_for_rect (lattice_for PosSet)
          (fun y' : PosSet =>
           constant
             (if collapse_might_be_empty then PosSet_inter x y' else y')) l0)) l2
.
Proof.
intros.
(* This should not capture a variable *)
Fail rewrite lattice_rewrite.
Abort.
