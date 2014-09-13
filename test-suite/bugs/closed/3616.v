(* Was failing from April 2014 to September 2014 because of injection *)
Goal forall P e es t, (e :: es = existT P tt t :: es)%list -> True.
inversion 1.
