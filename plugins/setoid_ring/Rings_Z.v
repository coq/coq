Require Export Cring.
Require Export Integral_domain.
Require Export Ncring_initial.

Instance Zcri: (Cring (Rr:=Zr)).
red. exact Zmult_comm. Defined.

Lemma Z_one_zero: 1%Z <> 0%Z.
omega. 
Qed.

Instance Zdi : (Integral_domain (Rcr:=Zcri)). 
constructor. 
exact Zmult_integral. exact Z_one_zero. Defined.
