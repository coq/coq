(* About binders which remain unnamed after typing *)

Global Set Asymmetric Patterns.

Definition proj2_sig_map {A} {P Q : A -> Prop} (f : forall a, P a -> Q a) (x :
@sig A P) : @sig A Q
  := let 'exist a p := x in exist Q a (f a p).
Axioms (feBW' : Type) (g : Prop -> Prop) (f' : feBW' -> Prop).
Definition foo := @proj2_sig_map feBW' (fun  H  => True = f' _) (fun H =>
 g True = g (f' H))
                                 (fun (a : feBW') (p : (fun H : feBW' => True =
 f' H) a) => @f_equal Prop Prop g True (f' a) p).
Print foo.
Goal True.
  lazymatch type of foo with
  | sig (fun a : ?A => ?P) -> _
    => pose (fun a : A => a = a /\ P = P)
  end.
