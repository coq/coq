(* Testing of various things about Print Ltac *)
(* https://github.com/coq/coq/issues/10971 *)
Ltac t1 := time "my tactic" idtac.
Print Ltac t1.
Ltac t2 := let x := string:("my tactic") in idtac x.
Print Ltac t2.
Tactic Notation "idtacstr" string(str) := idtac str.
Ltac t3 := idtacstr "my tactic".
Print Ltac t3.
(* https://github.com/coq/coq/issues/9716 *)
Ltac t4 x := match x with ?A => constr:((A, A)) end.
Print Ltac t4.

Notation idnat := (@id nat).
Notation idn := id.
Notation idan := (@id).
Fail Strategy transparent [idnat].
Strategy transparent [idn].
Strategy transparent [idan].
Ltac withstrategy l x :=
  let idx := smart_global:(id) in
  let tl := strategy_level:(transparent) in
  with_strategy 1 [id id] (
  with_strategy l [id id] (
  with_strategy tl [id id] (
  with_strategy 0 [id id] (
  with_strategy transparent [id id] (
  with_strategy opaque [id id] (
  with_strategy expand [id id] (
  with_strategy 0 [idx] (
  with_strategy 0 [id x] (
  with_strategy 0 [x id] (
  with_strategy 0 [idn] (
  with_strategy 0 [idn x] (
  with_strategy 0 [idn id] (
  with_strategy 0 [idn id x] (
  with_strategy 0 [idan] (
  with_strategy 0 [idan x] (
  with_strategy 0 [idan id] (
  with_strategy 0 [idan id x] (
  idtac
    )))))))))))))))))).
Print Ltac withstrategy.

Module Type Empty. End Empty.
Module E. End E.
Module F (E : Empty).
  Definition id {T} := @id T.
  Notation idnat := (@id nat).
  Notation idn := id.
  Notation idan := (@id).
  Fail Strategy transparent [idnat].
  Strategy transparent [idn].
  Strategy transparent [idan].
  Ltac withstrategy l x :=
    let idx := smart_global:(id) in
    let tl := strategy_level:(transparent) in
    with_strategy 1 [id id] (
    with_strategy l [id id] (
    with_strategy tl [id id] (
    with_strategy 0 [id id] (
    with_strategy transparent [id id] (
    with_strategy opaque [id id] (
    with_strategy expand [id id] (
    with_strategy 0 [idx] (
    with_strategy 0 [id x] (
    with_strategy 0 [x id] (
    with_strategy 0 [idn] (
    with_strategy 0 [idn x] (
    with_strategy 0 [idn id] (
    with_strategy 0 [idn id x] (
    with_strategy 0 [idan] (
    with_strategy 0 [idan x] (
    with_strategy 0 [idan id] (
    with_strategy 0 [idan id x] (
    idtac
      )))))))))))))))))).
  Print Ltac withstrategy.
End F.

Module FE := F E.
Print Ltac FE.withstrategy.
