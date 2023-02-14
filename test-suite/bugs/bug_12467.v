Module ClosedBinder.

Notation "'WITH' ( x1 : t1 ) , x2t2 , .. , xntn  'PRE'  [ ] P 'POST' [ ] Q" :=
  ((fun x1 : t1 => (fun x2t2 => .. (fun xntn => (pair .. (pair x1 x2t2) .. xntn)) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => P) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => Q) .. )))
    (at level 200, x1 at level 0, x2t2 closed binder, P at level 100, Q at level 100, only parsing).
Check WITH (x : nat) , (y : nat) , (z : nat) PRE [] (x, y, z) POST [] (z, y, x).

End ClosedBinder.

Module OpenBinder.

(* Not eligible as an open binder because of the separating comma *)
Fail Notation "'WITH' ( x1 : t1 ) , x2t2 , .. , xntn  'PRE'  [ ] P 'POST' [ ] Q" :=
  ((fun x1 : t1 => (fun x2t2 => .. (fun xntn => (pair .. (pair x1 x2t2) .. xntn)) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => P) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => Q) .. )))
    (at level 200, x1 at level 0, x2t2 binder, P at level 100, Q at level 100, only parsing).

End OpenBinder.

Module Constr.

Notation "'WITH' ( x1 : t1 ) , x2t2 , .. , xntn  'PRE'  [ ] P 'POST' [ ] Q" :=
  ((fun x1 : t1 => (fun x2t2 => .. (fun xntn => (pair .. (pair x1 x2t2) .. xntn)) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => P) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => Q) .. )))
    (at level 200, x1 at level 0, x2t2, P at level 100, Q at level 100, only parsing).
(* Fail because, constr used for binder defaults to name *)
Fail Check WITH (x : nat) , (y : nat) , (z : nat) PRE [] (x, y, z) POST [] (z, y, x).

End Constr.

Module ConstrAsPattern.

Notation "'WITH' ( x1 : t1 ) , x2t2 , .. , xntn  'PRE'  [ ] P 'POST' [ ] Q" :=
  ((fun x1 : t1 => (fun x2t2 => .. (fun xntn => (pair .. (pair x1 x2t2) .. xntn)) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => P) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => Q) .. )))
    (at level 200, x1 at level 0, x2t2 constr as pattern, P at level 100, Q at level 100, only parsing).
Check WITH (x : nat) , (y : nat) , (z : nat) PRE [] (x, y, z) POST [] (z, y, x).

End ConstrAsPattern.

Module Pattern.

Notation "'WITH' ( x1 : t1 ) , x2t2 , .. , xntn  'PRE'  [ ] P 'POST' [ ] Q" :=
  ((fun x1 : t1 => (fun x2t2 => .. (fun xntn => (pair .. (pair x1 x2t2) .. xntn)) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => P) .. )),
   (fun x1 : t1 => (fun x2t2 => .. (fun xntn => Q) .. )))
    (at level 200, x1 at level 0, x2t2 pattern, P at level 100, Q at level 100, only parsing).
Check WITH (x : nat) , (y : nat) , (z : nat) PRE [] (x, y, z) POST [] (z, y, x).

End Pattern.

Module OnlyRecursiveBinderPartOfIssue17904.

Notation "∀ x .. y , P" := (forall x , .. (forall y , P) .. )
  (at level 200, x constr at level 8 as pattern, right associativity,
      format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
Check ∀ a b, a + b = 0.

End OnlyRecursiveBinderPartOfIssue17904.
