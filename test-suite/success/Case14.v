(* Test of inference of elimination predicate for "if" *)
(* submitted by Robert R Schneck *)

Axiom bad : false = true.

Definition try1 : False :=
  match bad in (_ = b) return (if b then False else True) with
  | refl_equal => I
  end.

Definition try2 : False :=
  match bad in (_ = b) return ((if b then False else True):Prop) with
  | refl_equal => I
  end.

Definition try3 : False :=
  match
    bad in (_ = b) return ((fun b' : bool => if b' then False else True) b)
  with
  | refl_equal => I
  end.
