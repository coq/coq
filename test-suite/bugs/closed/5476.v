Require Setoid.

Goal forall (P : Prop) (T : Type) (m m' : T) (T0 T1 : Type) (P2 : forall _ : 
Prop, Prop) 
            (P0 : Set) (x0 : P0) (P1 : forall (_ : P0) (_ : T), Prop)
            (P3 : forall (_ : forall (_ : P0) (_ : T0) (_ : Prop), Prop) (_ : 
T) (_ : Prop), Prop)
            (o : forall _ : P0, option T1)
            (_ : P3
                   (fun (k : P0) (_ : T0) (_ : Prop) =>
                      match o k return Prop with
                      | Some _ => True
                      | None => False
                      end) m' P) (_ : P2 (P1 x0 m))
            (_ : forall (f : forall (_ : P0) (_ : T0) (_ : Prop), Prop) (m1 m2 
: T) 
                        (k : P0) (e : T0) (_ : P2 (P1 k m1)), iff (P3 f m2 P) 
(f k e (P3 f m1 P))), False.
Proof.
  intros ???????????? H0 H H1.
  rewrite H1 in H0; eauto with nocore.
  { lazymatch goal with
    | H : match ?X with _ => _ end |- _
      => first [ lazymatch goal with
                 | [ H' : context[X] |- _ ] => idtac H
                 end
               | fail 1 "could not find" X ]
    end.
