Goal forall (A B : Type) (P : forall _ : prod A B, Type) (a : A) (b : B) (p p0 : forall (x : A) (x' : B), P (@pair A B x x')),
    @eq (P (@pair A B a b)) (p (@fst A B (@pair A B a b)) (@snd A B (@pair A B a b)))
        (p0 (@fst A B (@pair A B a b)) (@snd A B (@pair A B a b))).
Proof.
  intros.
  Fail generalize dependent (a, b).
