(* Call of apply on <-> failed because of evars in elimination predicate *)
Generalizable Variables patch.

Class Patch (patch : Type) := {
    commute : patch -> patch -> Prop
}.

Parameter flip : forall	`{patchInstance	: Patch	patch}
                       	 {a b : patch},
                 commute a b <-> commute b a.

Lemma Foo : forall `{patchInstance : Patch patch}
                    {a b : patch},
            (commute a b)
         -> True.
Proof.
intros.
apply flip in H.

(* failed in well-formed arity check because elimination predicate of
   iff in (@flip _ _ _ _) had normalized evars while the ones in the
   type of (@flip _ _ _ _) itself had non-normalized evars *)

(* By the way, is the check necessary ? *)
