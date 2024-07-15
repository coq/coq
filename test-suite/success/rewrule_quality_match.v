(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

#[universes(polymorphic)] Symbol irrel@{q|u|} : forall {A : Type@{q|u}}, A -> bool.

Rewrite Rule id_rew :=
| irrel@{SProp|_} _ => true
| irrel@{Type|_} _ => false.

Inductive STrue : SProp := SI.

Goal True.
  let c := constr:((irrel SI, irrel tt)) in
  let cl := eval lazy in c in
  constr_eq cl (true, false).

  let c := constr:((irrel SI, irrel tt)) in
  let cl := eval cbv in c in
  constr_eq cl (true, false).

  let c := constr:((irrel SI, irrel tt)) in
  let cl := eval cbn in c in
  constr_eq cl (true, false).

  let c := constr:((irrel SI, irrel tt)) in
  let cl := eval simpl in c in
  constr_eq cl (true, false).

  exact I.
Qed.
