(* L'algo d'inférence du prédicat doit gérer le K-rédex dans le type de b *)
(* Problème rapporté par Solange Coupet *)

Section A.

Variables Alpha:Set; Beta:Set.

Definition nodep_prod_of_dep: (sigS Alpha [a:Alpha]Beta)-> Alpha*Beta:=
[c] Cases c of (existS a b)=>(a,b) end.

End A.
