(* L'algo d'inférence du prédicat doit gérer le K-rédex dans le type de b *)
(* Problème rapporté par Solange Coupet *)

Section A.

Variables (Alpha : Set) (Beta : Set).

Definition nodep_prod_of_dep (c : sigS (fun a : Alpha => Beta)) :
  Alpha * Beta := match c with
                  | existS a b => (a, b)
                  end.

End A.
