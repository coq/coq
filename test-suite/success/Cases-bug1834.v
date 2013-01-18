(* Bug in the computation of generalization *)

(* The following bug, elaborated by Bruno Barras, is solved from r11083  *)

Parameter P : unit -> Prop.
Definition T := sig P.
Parameter Q : T -> Prop.
Definition U := sig Q.
Parameter a : U.
Check (match a with exist _ (exist _ tt e2) e3 => e3=e3 end).

(* There is still a form submitted by Pierre Corbineau (#1834) which fails *)

