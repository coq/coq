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
Implicit Arguments Nil [pu cxt].
Implicit Arguments Cons [pu from mid to].

Program Fixpoint insertBase {pu : PatchUniverse}
                            {from mid to : NameSet}
                            (p : pu_type from mid)
                            (qs : SequenceBase pu mid to)
                          : SequenceBase pu from to
    := match qs with
       | Nil _ => Cons p Nil
       | Cons mid' mid2' to' q qs' =>
           match SignedName_compare (pu_nameOf p) (pu_nameOf q) with
           | Lt => Cons p qs
           | _  => match commutable_dec p (castPatchFrom _ q) with
                   | inleft (existT _ (existT q' (existT p' _))) => Cons q'
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
