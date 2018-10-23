(* L'algo d'inférence du prédicat doit gérer le K-rédex dans le type de b *)
(* Problème rapporté par Solange Coupet *)

Section A.

Variables (Alpha : Set) (Beta : Set).

Definition nodep_prod_of_dep (c : sigT (fun a : Alpha => Beta)) :
  Alpha * Beta := match c with
                  | existT _ a b => (a, b)
                  end.

End A.
