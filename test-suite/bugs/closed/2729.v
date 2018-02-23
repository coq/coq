(* This bug report actually revealed two bugs in the reconstruction of
   a term with "match" in the vm *)

(* A simplified form of the first problem *)

(* Reconstruction of terms normalized with vm when a constructor has *)
(* let-ins arguments *)

Record A : Type := C { a := 0 : nat; b : a=a }.
Goal forall d:A, match d with C a b => b end = match d with C a b => b end.
intro.
vm_compute.
(* Now check that it is well-typed *)
match goal with |- ?c = _ => first [let x := type of c in idtac | fail 2] end.
Abort.

(* A simplified form of the second problem *)

Parameter P : nat -> Type.

Inductive box A := Box : A -> box A.

Axiom com : {m : nat & box (P m) }.

Lemma L :
  (let (w, s) as com' return (com' = com -> Prop) := com in
   let (s0) as s0
     return (existT (fun m : nat => box (P m)) w s0 = com -> Prop) := s in
   fun _ : existT (fun m : nat => box (P m)) w (Box (P w) s0) = com =>
   True) eq_refl.
Proof.
vm_compute.
(* Now check that it is well-typed (the "P w" used to be turned into "P s") *)
match goal with |- ?c => first [let x := type of c in idtac | fail 2] end.
Abort.

(* Then the original report *)

Require Import Equality.

Parameter NameSet : Set.
Parameter SignedName : Set.
Parameter SignedName_compare : forall (x y : SignedName), comparison.
Parameter pu_type : NameSet -> NameSet -> Type.
Parameter pu_nameOf : forall {from to : NameSet}, pu_type from to -> SignedName.
Parameter commute : forall {from mid1 mid2 to : NameSet},
              pu_type from mid1 -> pu_type mid1 to
           -> pu_type from mid2 -> pu_type mid2 to -> Prop.

Program Definition castPatchFrom {from from' to : NameSet}
                                 (HeqFrom : from = from')
                                 (p : pu_type from to)
                               : pu_type from' to
    := p.

Class PatchUniverse : Type := mkPatchUniverse {

    commutable : forall {from mid1 to : NameSet},
                        pu_type from mid1 -> pu_type mid1 to -> Prop
        := fun {from mid1 to : NameSet}
               (p : pu_type from mid1) (q : pu_type mid1 to) =>
           exists mid2   : NameSet,
           exists q' : pu_type from mid2,
           exists p' : pu_type mid2 to,
           commute p q q' p';

    commutable_dec : forall {from mid to : NameSet}
                            (p : pu_type from mid)
                            (q : pu_type mid to),
                     {mid2 : NameSet &
                     { q' : pu_type from mid2 &
                     { p' : pu_type mid2 to &
                     commute p q q' p' }}}
                   + {~(commutable p q)}
}.

Inductive SequenceBase (pu : PatchUniverse)
                     : NameSet -> NameSet -> Type
    := Nil : forall {cxt : NameSet},
             SequenceBase pu cxt cxt
     | Cons : forall {from mid to : NameSet}
                     (p : pu_type from mid)
                     (qs : SequenceBase pu mid to),
              SequenceBase pu from to.
Arguments Nil [pu cxt].
Arguments Cons [pu from mid to].

Program Fixpoint insertBase {pu : PatchUniverse}
                            {from mid to : NameSet}
                            (p : pu_type from mid)
                            (qs : SequenceBase pu mid to)
                          : SequenceBase pu from to
    := match qs with
       | Nil => Cons p Nil
       | Cons q qs' =>
           match SignedName_compare (pu_nameOf p) (pu_nameOf q) with
           | Lt => Cons p qs
           | _  => match commutable_dec p (castPatchFrom _ q) with
                   | inleft (existT _ _ (existT _ q' (existT _ p' _))) => Cons q'
(insertBase p' qs')
                   | inright _ => Cons p qs
                   end
           end
       end.

Lemma insertBaseConsLt {pu : PatchUniverse}
                       {o op opq opqr : NameSet}
                       (p : pu_type o op)
                       (q : pu_type op opq)
                       (rs : SequenceBase pu opq opqr)
                       (p_Lt_q : SignedName_compare (pu_nameOf p) (pu_nameOf q)
= Lt)
                     : insertBase p (Cons q rs) = Cons p (Cons q rs).
Proof.
vm_compute.
