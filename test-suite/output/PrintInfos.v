About existT.
Print existT.
Print Implicit existT.

Print eq_refl.
About eq_refl.
Print Implicit eq_refl.

Print plus.
About plus.
Print Implicit plus.

About plus_n_O.

Implicit Arguments le_S [[n] m].
Print le_S.

About comparison.
Print comparison.

Definition foo := forall x, x = 0.
Parameter bar : foo.
Implicit Arguments bar [x].
About bar.
Print bar.

About Peano. (* Module *)
About existS2. (* Notation *)

Implicit Arguments eq_refl [[A] [x]] [[A]].
Print eq_refl.
