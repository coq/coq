Inductive testI : bool -> Type :=
| testItrue : testI true
| testIfalse : testI false
.

Definition testFgood (b : bool) (x : testI b) :
if b then b = b else b = b.
Proof.
refine (
match x as x0 in testI b0 return
  if b0 return Prop then b0 = b0 else b0 = b0
with
| testItrue => eq_refl
| testIfalse => eq_refl
end
).
Qed.

Definition testFbad (b : bool) (x : testI b) :
if b then b = b else b = b.
Proof.
refine (
match x as x0 in testI b0 return
  if b0 then b0 = b0 else b0 = b0
with
| testItrue => eq_refl
| testIfalse => eq_refl
end
).
Qed.
