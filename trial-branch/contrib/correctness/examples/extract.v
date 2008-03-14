
(* Tests d'extraction *)

Require ProgramsExtraction.
Save State Ici "test extraction".

(* exp *)

Require exp.
Write Caml File "exp" [ i_exp r_exp ].

(* exp_int *)

Restore State Ici.
Require exp_int.
Write Caml File "exp_int" [ i_exp r_exp ].

(* fact *)

Restore State Ici.
Require fact.
Initialize x with (S (S (S O))).
Initialize y with O.
Write Caml File "fact" [ factorielle ].

(* fact_int *)

Restore State Ici.
Require fact_int.
Initialize x with `3`.
Initialize y with `0`.
Write Caml File "fact_int" [ factorielle ].

(* Handbook *)

Restore State Ici.
Require Handbook.
Initialize X with `3`.
Initialize Y with `3`.
Initialize Z with `3`.
Initialize N with `3`.
Initialize S with `3`.
Write Caml File "Handbook" [ pgm178 pgm186 pgm196 ].
