Module Wish11692.

(* Support for let-in in clear dependent *)

Goal forall x : Prop, let z := 0 in let z' : (fun _ => True) x := I in let y := x in y -> True.
Proof. intros x z z' y H. clear dependent x. Show. exact I. Qed.

End Wish11692.
