From Stdlib Require Program.Tactics.

Module Reduced.
  Axiom t : Type -> Type.
  Axiom map2 : forall {elt : Type}, t elt.

  Program Definition map2' elt : t elt
    := let f' := match true with
                 | true => @None elt
                 | _ => None
                 end
       in
       map2.
(* Error: Unbound reference: In environment
elt : Type
The reference 2 is free.
 *)
  About map2'.
End Reduced.

From Stdlib Require FMapInterface.
Import Orders.
Import Stdlib.FSets.FMapInterface.

Definition option_value {A} (v1 : option A) (v2 : A) : A := match v1 with Some v => v | None => v2 end.

Module ProdWSfun_gen (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) (M1 : WSfun E1) (M2 : WSfun E2).

  Definition t elt := M1.t { m : M2.t elt | ~M2.Empty m }.
  Program Definition map2 elt elt' elt'' (f : option elt -> option elt' -> option elt'') : t elt -> t elt' -> t elt''
    := let f' := match f None None with
                 | None => f
                 | _ => fun x y => match x, y with
                                   | None, None => None
                                   | _, _ => f x y
                                   end
                 end in
       M1.map2 (fun m1 m2
                => if match m1, m2 with None, None => true | _, _ => false end
                   then None
                   else
                     let m1' := option_value (option_map (@proj1_sig _ _) m1) (M2.empty _) in
                     let m2' := option_value (option_map (@proj1_sig _ _) m2) (M2.empty _) in
                     let m' := M2.map2 f' m1' m2' in
                     if M2.is_empty m'
                     then None
                     else Some (exist _ m' _)).
  (* uncaught Not_found *)
  Next Obligation. Admitted.
  About map2.

End ProdWSfun_gen.
