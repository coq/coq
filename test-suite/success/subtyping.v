(* Testing comparison of terms inside their type in the presence of
   contravariant subtyping *)

Axiom E : (Set -> Set) -> Set.
Axiom C : forall X, E X.

(* Here, (fun X:Type => True) should be the same as (fun X:Set => True)
   when seen as inhabitants of (Set->Set) *)

Check C (fun X : Type => True) : E (fun X : Set => True).
