(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

#[universes(polymorphic)] Symbol dispatch@{q;u} : forall {A : Univ@{q;u}}, A -> nat.

Sort s.

Rewrite Rule id_rew :=
| dispatch@{SProp;_} _ => 0
| dispatch@{Type;_} _ => 1
| dispatch@{s;_} _ => 2.

Inductive STrue : SProp := SI.

#[universes(template=no)]
Inductive sTrue : Univ@{s;_} := sI.

Goal True.
  let c := constr:((dispatch SI, dispatch tt, dispatch sI)) in
  let cl := eval lazy in c in
  constr_eq cl (0, 1, 2).

  let c := constr:((dispatch SI, dispatch tt, dispatch sI)) in
  let cl := eval cbv in c in
  constr_eq cl (0, 1, 2).

  let c := constr:((dispatch SI, dispatch tt, dispatch sI)) in
  let cl := eval cbn in c in
  constr_eq cl (0, 1, 2).

  let c := constr:((dispatch SI, dispatch tt, dispatch sI)) in
  let cl := eval simpl in c in
  constr_eq cl (0, 1, 2).

  exact I.
Qed.
