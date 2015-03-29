Lemma foo : True.
Proof.
pose (fun x : nat => (let H:=true in x)) as s.
match eval cbv delta [s] in s with
| context C[true] =>
  let C':=context C[false] in pose C' as s'
end.
