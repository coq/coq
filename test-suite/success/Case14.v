(* Test of inference of elimination predicate for "if" *)
(* submitted by Robert R Schneck *)

Axiom bad : false = true.

Definition try1 : False :=
  <[b:bool][_:false=b](if b then False else True)>
  Cases bad of refl_equal => I end.

Definition try2 : False :=
  <[b:bool][_:false=b]((if b then False else True)::Prop)>
  Cases bad of refl_equal => I end.

Definition try3 : False :=
  <[b:bool][_:false=b](([b':bool] if b' then False else True) b)>
  Cases bad of refl_equal => I end.
