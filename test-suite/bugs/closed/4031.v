Definition something (P:Type) (e:P) := e.

Inductive myunit : Set := mytt.
  (* Proof below works when definition is in Type,
     however builtin types such as unit are in Set. *)

Lemma demo_hide_generic : 
   let x := mytt in x = x.
Proof.
  intros.
  change mytt with (@something _ mytt) in x.
  subst x. (* Proof works if this line is removed *)
  reflexivity.
Qed.
