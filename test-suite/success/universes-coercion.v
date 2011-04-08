(* This example used to emphasize the absence of LEGO-style universe
   polymorphism; Matthieu's improvements of typing on 2011/3/11 now
   makes (apparently) that Amokrane's automatic eta-expansion in the
   coercion mechanism works; this makes its illustration as a "weakness"
   of universe polymorphism obsolete (example submitted by Randy Pollack).

   Note that this example is not an evidence that the current
   non-kernel eta-expansion behavior is the most expected one.  
*)

Parameter K : forall T : Type, T -> T.
Check (K (forall T : Type, T -> T) K).

(*
   note that the inferred term is
     "(K (forall T (* u1 *) : Type, T -> T) (fun T:Type (* u1 *) => K T))"
   which is not eta-equivalent to 
     "(K (forall T : Type, T -> T) K"
   because the eta-expansion of the latter
     "(K (forall T : Type, T -> T) (fun T:Type (* u2 *) => K T)"
  assuming K of type "forall T (* u2 *) : Type, T -> T"
*)
