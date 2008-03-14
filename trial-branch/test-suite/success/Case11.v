(* L'algo d'inf�rence du pr�dicat doit g�rer le K-r�dex dans le type de b *)
(* Probl�me rapport� par Solange Coupet *)

Section A.

Variables (Alpha : Set) (Beta : Set).

Definition nodep_prod_of_dep (c : sigS (fun a : Alpha => Beta)) :
  Alpha * Beta := match c with
                  | existS a b => (a, b)
                  end.

End A.
