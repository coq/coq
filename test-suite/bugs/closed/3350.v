Require Import TestSuite.admit.
Require Coq.Vectors.Fin.
Require Coq.Vectors.Vector.

Local Generalizable All Variables.
Set Implicit Arguments.

Arguments Fin.F1 : clear implicits.

Lemma fin_0_absurd : notT (Fin.t 0).
Proof. hnf. apply Fin.case0. Qed.

Axiom admit : forall {A}, A.

Fixpoint lower {n:nat} (p:Fin.t (S n)) {struct p} :
  forall (i:Fin.t (S n)), option (Fin.t n)
  := match p in Fin.t (S n1)
           return Fin.t (S n1) -> option (Fin.t n1)
     with
       | @Fin.F1 n1 =>
         fun (i:Fin.t (S n1)) =>
           match i in Fin.t (S n2) return option (Fin.t n2) with
             | @Fin.F1 n2 => None
             | @Fin.FS n2 i2 => Some i2
           end
       | @Fin.FS n1 p1 =>
         fun (i:Fin.t (S n1)) =>
           match i in Fin.t (S n2) return Fin.t n2 -> option (Fin.t n2) with
             | @Fin.F1 n2 =>
               match n2 as n3 return Fin.t n3 -> option (Fin.t n3) with
                 | 0 => fun p2 => False_rect _ (fin_0_absurd p2)
                 | S n3 => fun p2 => Some (Fin.F1 n3)
               end
             | @Fin.FS n2 i2 =>
               match n2 as n3 return Fin.t n3 -> Fin.t n3 -> option (Fin.t n3) with
                 | 0 => fun i3 p3 => False_rect _ (fin_0_absurd p3)
                 | S n3 => fun (i3 p3:Fin.t (S n3)) =>
                             option_map (@Fin.FS _) admit
               end i2
           end p1
     end.

Lemma lower_ind (P: forall n (p i:Fin.t (S n)), option (Fin.t n) -> Prop)
      (c11 : forall n, P n (Fin.F1 n) (Fin.F1 n) None)
      (c1S : forall n (i:Fin.t n), P n (Fin.F1 n) (Fin.FS i) (Some i))
      (cS1 : forall n (p:Fin.t (S n)),
               P (S n) (Fin.FS p) (Fin.F1 (S n)) (Some (Fin.F1 n)))
      (cSSS : forall n (p i:Fin.t (S n)) (i':Fin.t n)
                     (Elow:lower p i = Some i'),
                P n p i (Some i') ->
                P (S n) (Fin.FS p) (Fin.FS i) (Some (Fin.FS i')))
      (cSSN : forall n (p i:Fin.t (S n))
                (Elow:lower p i = None),
                P n p i None ->
                P (S n) (Fin.FS p) (Fin.FS i) None) :
  forall n (p i:Fin.t (S n)), P n p i (lower p i).
Proof.
  fix lower_ind 2. intros n p.
  refine (match p as p1 in Fin.t (S n1)
                return forall (i1:Fin.t (S n1)), P n1 p1 i1 (lower p1 i1)
          with
            | @Fin.F1 n1 => _
            | @Fin.FS n1 p1 => _
          end); clear n p.
  { revert n1. refine (@Fin.caseS _ _ _); cbn; intros.
    apply c11. apply c1S. }
  { intros i1. revert p1.
    pattern n1, i1; refine (@Fin.caseS _ _ _ _ _);
    clear n1 i1;
    (intros [|n] i; [refine (False_rect _ (fin_0_absurd i)) | cbn ]).
    { apply cS1. }
    { intros p. pose proof (admit : P n p i (lower p i)) as H.
      destruct (lower p i) eqn:E.
      { admit; assumption. }
      { cbn. apply admit; assumption. } } }
Qed.

Section squeeze.
  Context {A:Type} (x:A).
  Notation vec := (Vector.t A).

  Fixpoint squeeze {n} (v:vec n) (i:Fin.t (S n)) {struct i} : vec (S n) :=
    match i in Fin.t (S _n) return vec _n -> vec (S _n)
    with
      | @Fin.F1 n' => fun v' => Vector.cons _ x _ v'
      | @Fin.FS n' i' =>
        fun v' =>
          match n' as _n return vec _n -> Fin.t _n -> vec (S _n)
          with
            | 0 => fun u i' => False_rect _ (fin_0_absurd i')
            | S m =>
              fun (u:vec (S m)) =>
                match u in Vector.t _ (S _m)
                      return Fin.t (S _m) -> vec (S (S _m))
                with
                  | Vector.nil _ => tt
                  | Vector.cons _ h _ u' =>
                    fun j' => Vector.cons _ h _ admit (* (squeeze u' j') *)
                end
          end v' i'
    end v.
End squeeze.

Require Import Program.
Lemma squeeze_nth (A:Type) (x:A) (n:nat) (v:Vector.t A n) p i :
  Vector.nth (squeeze x v p) i = match lower p i with
                                   | Some j => Vector.nth v j
                                   | None => x
                                 end.
Proof.
  (* alternatively: [functional induction (lower p i) using lower_ind] *)
  revert v. pattern n, p, i, (lower p i).
  refine (@lower_ind _ _ _ _ _ _ n p i);
    intros; cbn; auto.

  (*** Fails here with "Conversion test raised an anomaly" ***)
  revert v.
  admit.
  admit.
  admit.
Qed.
