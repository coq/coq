(* A disjoint-names condition was missing when matching names in Ltac
   pattern-matching *)

Goal True.
  let x := (eval cbv beta zeta in (fun P => let Q := P in fun P => P + Q)) in
  unify x (fun a b => b + a); (* success *)
    let x' := lazymatch x with
              | (fun (a : ?A) (b : ?B) => ?k)
                => constr:(fun (a : A) (b : B) => k)
              end in
    unify x x'.
Abort.
