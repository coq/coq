Set Definitional UIP.

Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.
Arguments srefl {_ _}.

(* Axiom implied by propext (so consistent) *)
Axiom all_eq : forall (P Q:Prop), P -> Q -> seq P Q.

Definition transport (P Q:Prop) (x:P) (y:Q) : Q
  := match all_eq P Q x y with srefl => x end.

Definition top : Prop := forall P : Prop, P -> P.

Definition c : top :=
  fun P p =>
    transport
      (top -> top)
      P
      (fun x : top => x (top -> top) (fun x => x) x)
      p.

Fail Timeout 1 Eval lazy in c (top -> top) (fun x => x) c.
(* loops *)
