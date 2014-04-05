(* Fixed together with #3262 in 48af6d1418282323b9fff0e789fed9478c064434 *)
(* April 4, 2014 (non-progress in candidates was not detected) *)

Definition eqbool_dep (P : bool -> Prop) (h1 : P true) (b : bool) (h2 : P b)
  : Prop :=
(match b (* return P b -> Prop *) with
 | true => fun (h : P true) => h1 = h
 | false => fun (_ : P false) => False
end (* : P b -> Prop *)) h2.
