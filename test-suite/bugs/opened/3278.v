Module a.
  Fail Check let x' := _ in
             $(exact x')$.

  Notation foo x := (let x' := x in $(exact x')$).

  Fail Check foo _. (* Error:
Cannot infer an internal placeholder of type "Type" in environment:

x' := ?42 : ?41
. *)
End a.

Module b.
  Notation foo x := (let x' := x in let y := ($(exact I)$ : True) in I).
  Notation bar x := (let x' := x in let y := (I : True) in I).

  Check let x' := _ in $(exact I)$. (* let x' := ?5 in I *)
  Check bar _. (* let x' := ?9 in let y := I in I *)
  Fail Check foo _. (* Error:
Cannot infer an internal placeholder of type "Type" in environment:

x' := ?42 : ?41
. *)
End b.
