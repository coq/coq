(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Peano_dec.
Require Ring.
Require Field_Compl.

Record Field_Theory : Type :=
{ A : Type;
  Aplus : A -> A -> A;
  Amult : A -> A -> A;
  Aone : A;
  Azero : A;
  Aopp : A -> A;
  Aeq : A -> A -> bool;
  Ainv : A -> A;
  Aminus : (field_rel_option A);
  Adiv : (field_rel_option A);
  RT : (Ring_Theory Aplus Amult Aone Azero Aopp Aeq);
  Th_inv_def : (n:A)~(n=Azero)->(Amult (Ainv n) n)=Aone
}.

(* The reflexion structure *)
Inductive ExprA : Set :=
| EAzero    : ExprA
| EAone    : ExprA
| EAplus : ExprA -> ExprA -> ExprA
| EAmult : ExprA -> ExprA -> ExprA
| EAopp  : ExprA -> ExprA
| EAinv  : ExprA -> ExprA
| EAvar  : nat -> ExprA.

(**** Decidability of equality ****)

Lemma eqExprA_O:(e1,e2:ExprA){e1=e2}+{~e1=e2}.
Proof.
  Double Induction e1 e2;Try Intros;
   Try (Left;Reflexivity) Orelse Try (Right;Discriminate).
  Elim (H1 e0);Intro y;Elim (H2 e);Intro y0;
    Try (Left; Rewrite y; Rewrite y0;Auto)
    Orelse (Right;Red;Intro;Inversion H3;Auto).
  Elim (H1 e0);Intro y;Elim (H2 e);Intro y0;
    Try (Left; Rewrite y; Rewrite y0;Auto)
    Orelse (Right;Red;Intro;Inversion H3;Auto).
  Elim (H0 e);Intro y.
  Left; Rewrite y; Auto.
  Right;Red; Intro;Inversion H1;Auto.
  Elim (H0 e);Intro y.
  Left; Rewrite y; Auto.
  Right;Red; Intro;Inversion H1;Auto.
  Elim (eq_nat_dec n n0);Intro y.
  Left; Rewrite y; Auto.
  Right;Red;Intro;Inversion H;Auto. 
Defined.

Definition eq_nat_dec := Eval Compute in Peano_dec.eq_nat_dec.
Definition eqExprA := Eval Compute in eqExprA_O.

(**** Generation of the multiplier ****)

Fixpoint mult_of_list [e:(listT ExprA)]: ExprA :=
  Cases e of
  | nilT => EAone
  | (consT e1 l1) => (EAmult e1 (mult_of_list l1))
  end.

Section Theory_of_fields.

Variable T : Field_Theory.

Local AT := (A T).
Local AplusT := (Aplus T).
Local AmultT := (Amult T).
Local AoneT := (Aone T).
Local AzeroT := (Azero T).
Local AoppT := (Aopp T).
Local AeqT := (Aeq T).
Local AinvT := (Ainv T).
Local RTT := (RT T).
Local Th_inv_defT := (Th_inv_def T).

Add Abstract Ring (A T) (Aplus T) (Amult T) (Aone T) (Azero T) (Aopp T) 
  (Aeq T) (RT T).

Add Abstract Ring AT AplusT AmultT AoneT AzeroT AoppT AeqT RTT.

(***************************)
(*    Lemmas to be used    *)
(***************************)

Lemma AplusT_sym:(r1,r2:AT)(AplusT r1 r2)=(AplusT r2 r1).
Proof.
  Intros;Ring.
Save.

Lemma AplusT_assoc:(r1,r2,r3:AT)(AplusT (AplusT r1 r2) r3)=
                                (AplusT r1 (AplusT r2 r3)).
Proof.
  Intros;Ring.
Save.

Lemma AmultT_sym:(r1,r2:AT)(AmultT r1 r2)=(AmultT r2 r1).
Proof.
  Intros;Ring.
Save.

Lemma AmultT_assoc:(r1,r2,r3:AT)(AmultT (AmultT r1 r2) r3)=
                                (AmultT r1 (AmultT r2 r3)).
Proof.
  Intros;Ring.
Save.

Lemma AplusT_Ol:(r:AT)(AplusT AzeroT r)=r.
Proof.
  Intros;Ring.
Save.

Lemma AmultT_1l:(r:AT)(AmultT AoneT r)=r.
Proof.
  Intros;Ring.
Save.

Lemma AplusT_AoppT_r:(r:AT)(AplusT r (AoppT r))=AzeroT.
Proof.
  Intros;Ring.
Save.

Lemma AmultT_AplusT_distr:(r1,r2,r3:AT)(AmultT r1 (AplusT r2 r3))=
                        (AplusT (AmultT r1 r2) (AmultT r1 r3)).
Proof.
  Intros;Ring.
Save.

Lemma r_AplusT_plus:(r,r1,r2:AT)(AplusT r r1)=(AplusT r r2)->r1=r2.
Proof.
  Intros; Transitivity (AplusT (AplusT (AoppT r) r) r1).
  Ring.
  Transitivity (AplusT (AplusT (AoppT r) r) r2).
  Repeat Rewrite -> AplusT_assoc; Rewrite <- H; Reflexivity.
  Ring.
Save.
 
Lemma r_AmultT_mult:
  (r,r1,r2:AT)(AmultT r r1)=(AmultT r r2)->~r=AzeroT->r1=r2.
Proof.
  Intros; Transitivity (AmultT (AmultT (AinvT r) r) r1).
  Rewrite Th_inv_defT;[Symmetry; Apply AmultT_1l;Auto|Auto].
  Transitivity (AmultT (AmultT (AinvT r) r) r2).
  Repeat Rewrite AmultT_assoc; Rewrite H; Trivial.
  Rewrite Th_inv_defT;[Apply AmultT_1l;Auto|Auto].
Save.

Lemma AmultT_Or:(r:AT) (AmultT r AzeroT)=AzeroT.
Proof.
  Intro; Ring.
Save.
 
Lemma AmultT_Ol:(r:AT)(AmultT AzeroT r)=AzeroT.
Proof.
  Intro; Ring.
Save.
 
Lemma AmultT_1r:(r:AT)(AmultT r AoneT)=r.
Proof.
  Intro; Ring.
Save.
 
Lemma AinvT_r:(r:AT)~r=AzeroT->(AmultT r (AinvT r))=AoneT.
Proof.
  Intros; Rewrite -> AmultT_sym; Apply Th_inv_defT; Auto.
Save.
 
Lemma without_div_O_contr:
  (r1,r2:AT)~(AmultT r1 r2)=AzeroT ->~r1=AzeroT/\~r2=AzeroT.
Proof.
  Intros r1 r2 H; Split; Red; Intro; Apply H; Rewrite H0; Ring.
Save.

(************************)
(*    Interpretation    *)
(************************)

(**** ExprA --> A ****)

Fixpoint interp_ExprA [lvar:(listT (prodT AT nat));e:ExprA] : AT :=
  Cases e of
  | EAzero         => AzeroT
  | EAone          => AoneT
  | (EAplus e1 e2) => (AplusT (interp_ExprA lvar e1) (interp_ExprA lvar e2))
  | (EAmult e1 e2) => (AmultT (interp_ExprA lvar e1) (interp_ExprA lvar e2))
  | (EAopp e)      => ((Aopp T) (interp_ExprA lvar e))
  | (EAinv e)      => ((Ainv T) (interp_ExprA lvar e))
  | (EAvar n)      => (assoc_2nd AT nat eq_nat_dec lvar n AzeroT)
  end.

(************************)
(*    Simplification    *)
(************************)

(**** Associativity ****)

Definition merge_mult :=
  Fix merge_mult {merge_mult [e1:ExprA] : ExprA -> ExprA :=
  [e2:ExprA]Cases e1 of
  | (EAmult t1 t2) =>
    Cases t2 of
    | (EAmult t2 t3) => (EAmult t1 (EAmult t2 (merge_mult t3 e2)))
    | _ => (EAmult t1 (EAmult t2 e2))
    end
  | _ => (EAmult e1 e2)
  end}.

Fixpoint assoc_mult [e:ExprA] : ExprA :=
  Cases e of
  | (EAmult e1 e3) =>
    Cases e1 of
    | (EAmult e1 e2) =>
      (merge_mult (merge_mult (assoc_mult e1) (assoc_mult e2))
        (assoc_mult e3))
    | _ => (EAmult e1 (assoc_mult e3))
    end
  | _ => e
  end.

Definition merge_plus :=
  Fix merge_plus {merge_plus [e1:ExprA]:ExprA->ExprA:=
  [e2:ExprA]Cases e1 of
  | (EAplus t1 t2) =>
    Cases t2 of
    | (EAplus t2 t3) => (EAplus t1 (EAplus t2 (merge_plus t3 e2)))
    | _ => (EAplus t1 (EAplus t2 e2))
    end
  | _ => (EAplus e1 e2)
  end}.

Fixpoint assoc [e:ExprA] : ExprA :=
  Cases e of
  | (EAplus e1 e3) =>
    Cases e1 of
    | (EAplus e1 e2) =>
      (merge_plus (merge_plus (assoc e1) (assoc e2)) (assoc e3))
    | _ => (EAplus (assoc_mult e1) (assoc e3))
    end
  | _ => (assoc_mult e)
  end.

Lemma merge_mult_correct1:
  (e1,e2,e3:ExprA)(lvar:(listT (prodT AT nat)))
  (interp_ExprA lvar (merge_mult (EAmult e1 e2) e3))=
  (interp_ExprA lvar (EAmult e1 (merge_mult e2 e3))).
Proof.
Intros e1 e2;Generalize e1;Generalize e2;Clear e1 e2.
Induction e2;Auto;Intros.
Unfold 1 merge_mult;Fold merge_mult;
 Unfold 2 interp_ExprA;Fold interp_ExprA;
 Rewrite (H0 e e3 lvar);
 Unfold 1 interp_ExprA;Fold interp_ExprA;
 Unfold 5 interp_ExprA;Fold interp_ExprA;Auto.
Save.

Lemma merge_mult_correct:
  (e1,e2:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (merge_mult e1 e2))=
    (interp_ExprA lvar (EAmult e1 e2)).
Proof.
Induction e1;Auto;Intros.
Elim e0;Try (Intros;Simpl;Ring).
Unfold interp_ExprA in H2;Fold interp_ExprA in H2;
 Cut (AmultT (interp_ExprA lvar e2) (AmultT (interp_ExprA lvar e4) 
       (AmultT (interp_ExprA lvar e) (interp_ExprA lvar e3))))=
       (AmultT (AmultT (AmultT (interp_ExprA lvar e) (interp_ExprA lvar e4)) 
       (interp_ExprA lvar e2)) (interp_ExprA lvar e3)).
Intro H3;Rewrite H3;Rewrite <-H2;
 Rewrite merge_mult_correct1;Simpl;Ring.
Ring.
Save.

Lemma assoc_mult_correct1:(e1,e2:ExprA)(lvar:(listT (prodT AT nat)))
  (AmultT (interp_ExprA lvar (assoc_mult e1)) 
         (interp_ExprA lvar (assoc_mult e2)))=
  (interp_ExprA lvar (assoc_mult (EAmult e1 e2))).
Proof.
Induction e1;Auto;Intros.
Rewrite <-(H e0 lvar);Simpl;Rewrite merge_mult_correct;Simpl;
 Rewrite merge_mult_correct;Simpl;Auto.
Save.

Lemma assoc_mult_correct:
  (e:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (assoc_mult e))=(interp_ExprA lvar e).
Proof.
Induction e;Auto;Intros.
Elim e0;Intros.
Intros;Simpl;Ring.
Simpl;Rewrite (AmultT_1l (interp_ExprA lvar (assoc_mult e1)));
 Rewrite (AmultT_1l (interp_ExprA lvar e1)); Apply H0.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite merge_mult_correct;Simpl;Rewrite merge_mult_correct;Simpl;
 Rewrite AmultT_assoc;Rewrite assoc_mult_correct1;Rewrite H2;Simpl;
 Rewrite <-assoc_mult_correct1 in H1;
 Unfold 3 interp_ExprA in H1;Fold interp_ExprA in H1;
 Rewrite (H0 lvar) in H1;
 Rewrite (AmultT_sym (interp_ExprA lvar e3) (interp_ExprA lvar e1));
 Rewrite <-AmultT_assoc;Rewrite H1;Rewrite AmultT_assoc;Ring.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite (H0 lvar);Auto.
Save.

Lemma merge_plus_correct1:
  (e1,e2,e3:ExprA)(lvar:(listT (prodT AT nat)))
  (interp_ExprA lvar (merge_plus (EAplus e1 e2) e3))=
  (interp_ExprA lvar (EAplus e1 (merge_plus e2 e3))).
Proof.
Intros e1 e2;Generalize e1;Generalize e2;Clear e1 e2.
Induction e2;Auto;Intros.
Unfold 1 merge_plus;Fold merge_plus;
 Unfold 2 interp_ExprA;Fold interp_ExprA;
 Rewrite (H0 e e3 lvar);
 Unfold 1 interp_ExprA;Fold interp_ExprA;
 Unfold 5 interp_ExprA;Fold interp_ExprA;Auto.
Save.

Lemma merge_plus_correct:
  (e1,e2:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (merge_plus e1 e2))=
    (interp_ExprA lvar (EAplus e1 e2)).
Proof.
Induction e1;Auto;Intros.
Elim e0;Try Intros;Try (Simpl;Ring).
Unfold interp_ExprA in H2;Fold interp_ExprA in H2;
  Cut (AplusT (interp_ExprA lvar e2) (AplusT (interp_ExprA lvar e4) 
        (AplusT (interp_ExprA lvar e) (interp_ExprA lvar e3))))=
        (AplusT (AplusT (AplusT (interp_ExprA lvar e) (interp_ExprA lvar e4)) 
       (interp_ExprA lvar e2)) (interp_ExprA lvar e3)).
Intro H3;Rewrite H3;Rewrite <-H2;Rewrite merge_plus_correct1;Simpl;Ring.
Ring.
Save.

Lemma assoc_plus_correct:(e1,e2:ExprA)(lvar:(listT (prodT AT nat)))
  (AplusT (interp_ExprA lvar (assoc e1)) (interp_ExprA lvar (assoc e2)))=
  (interp_ExprA lvar (assoc (EAplus e1 e2))).
Proof.
Induction e1;Auto;Intros.
Rewrite <-(H e0 lvar);Simpl;Rewrite merge_plus_correct;Simpl;
 Rewrite merge_plus_correct;Simpl;Auto.
Save.

Lemma assoc_correct:
  (e:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (assoc e))=(interp_ExprA lvar e).
Proof.
Induction e;Auto;Intros.
Elim e0;Intros.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite merge_plus_correct;Simpl;Rewrite merge_plus_correct;
 Simpl;Rewrite AplusT_assoc;Rewrite assoc_plus_correct;Rewrite H2;
 Simpl;Apply (r_AplusT_plus (interp_ExprA lvar (assoc e1))
   (AplusT (interp_ExprA lvar (assoc e2))
     (AplusT (interp_ExprA lvar e3) (interp_ExprA lvar e1)))
   (AplusT (AplusT (interp_ExprA lvar e2) (interp_ExprA lvar e3))
        (interp_ExprA lvar e1)));Rewrite <-AplusT_assoc; 
 Rewrite (AplusT_sym (interp_ExprA lvar (assoc e1)) 
                    (interp_ExprA lvar (assoc e2)));
 Rewrite assoc_plus_correct;Rewrite H1;Simpl;Rewrite (H0 lvar);
 Rewrite <-(AplusT_assoc (AplusT (interp_ExprA lvar e2) 
            (interp_ExprA lvar e1))
 (interp_ExprA lvar e3) (interp_ExprA lvar e1));
 Rewrite (AplusT_assoc (interp_ExprA lvar e2) (interp_ExprA lvar e1)
                      (interp_ExprA lvar e3));
 Rewrite (AplusT_sym (interp_ExprA lvar e1) (interp_ExprA lvar e3));
 Rewrite <-(AplusT_assoc (interp_ExprA lvar e2) (interp_ExprA lvar e3)
                        (interp_ExprA lvar e1));Apply AplusT_sym.
Unfold assoc;Fold assoc;Unfold interp_ExprA;Fold interp_ExprA;
 Rewrite assoc_mult_correct;Rewrite (H0 lvar);Simpl;Auto.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite (H0 lvar);Auto.
Simpl;Rewrite (H0 lvar);Auto.
Unfold assoc;Fold assoc;Unfold interp_ExprA;Fold interp_ExprA;
 Rewrite assoc_mult_correct;Simpl;Auto.
Save.

(**** Distribution *****)

Fixpoint distrib_EAopp [e:ExprA] : ExprA :=
  Cases e of
  | (EAplus e1 e2) => (EAplus (distrib_EAopp e1) (distrib_EAopp e2))
  | (EAmult e1 e2) => (EAmult (distrib_EAopp e1) (distrib_EAopp e2))
  | (EAopp e) => (EAmult (EAopp EAone) (distrib_EAopp e))
  | e => e
  end.

Definition distrib_mult_right :=
  Fix distrib_mult_right {distrib_mult_right [e1:ExprA]:ExprA->ExprA:=
  [e2:ExprA]Cases e1 of
  | (EAplus t1 t2) =>
    (EAplus (distrib_mult_right t1 e2) (distrib_mult_right t2 e2))
  | _ => (EAmult e1 e2)
  end}.

Fixpoint distrib_mult_left [e1:ExprA] : ExprA->ExprA :=
  [e2:ExprA]
  Cases e1 of
  | (EAplus t1 t2) =>
    (EAplus (distrib_mult_left t1 e2) (distrib_mult_left t2 e2))
  | _ => (distrib_mult_right e2 e1)
  end.

Fixpoint distrib_main [e:ExprA] : ExprA :=
  Cases e of
  | (EAmult e1 e2) => (distrib_mult_left (distrib_main e1) (distrib_main e2))
  | (EAplus e1 e2) => (EAplus (distrib_main e1) (distrib_main e2))
  | (EAopp e) => (EAopp (distrib_main e))
  | _ => e
  end.

Definition distrib [e:ExprA] : ExprA := (distrib_main (distrib_EAopp e)).

Lemma distrib_mult_right_correct:
  (e1,e2:ExprA)(lvar:(listT (prodT AT nat)))
     (interp_ExprA lvar (distrib_mult_right e1 e2))=
     (AmultT (interp_ExprA lvar e1) (interp_ExprA lvar e2)).
Proof.
Induction e1;Try Intros;Simpl;Auto.
Rewrite AmultT_sym;Rewrite AmultT_AplusT_distr;
 Rewrite (H e2 lvar);Rewrite (H0 e2 lvar);Ring.
Save.

Lemma distrib_mult_left_correct:
  (e1,e2:ExprA)(lvar:(listT (prodT AT nat)))
     (interp_ExprA lvar (distrib_mult_left e1 e2))=
     (AmultT (interp_ExprA lvar e1)  (interp_ExprA lvar e2)).
Proof.
Induction e1;Try Intros;Simpl.
Rewrite AmultT_Ol;Rewrite distrib_mult_right_correct;Simpl;Apply AmultT_Or.
Rewrite distrib_mult_right_correct;Simpl;
 Apply AmultT_sym. 
Rewrite AmultT_sym;
 Rewrite (AmultT_AplusT_distr (interp_ExprA lvar e2) (interp_ExprA lvar e)
  (interp_ExprA lvar e0)); 
 Rewrite (AmultT_sym (interp_ExprA lvar e2) (interp_ExprA lvar e));
 Rewrite (AmultT_sym (interp_ExprA lvar e2) (interp_ExprA lvar e0));
 Rewrite (H e2 lvar);Rewrite (H0 e2 lvar);Auto.
Rewrite distrib_mult_right_correct;Simpl;Apply AmultT_sym.
Rewrite distrib_mult_right_correct;Simpl;Apply AmultT_sym.
Rewrite distrib_mult_right_correct;Simpl;Apply AmultT_sym.
Rewrite distrib_mult_right_correct;Simpl;Apply AmultT_sym.
Save.

Lemma distrib_correct:
  (e:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (distrib e))=(interp_ExprA lvar e).
Proof.
Induction e;Intros;Auto.
Simpl;Rewrite <- (H lvar);Rewrite <- (H0 lvar); Unfold distrib;Simpl;Auto.
Simpl;Rewrite <- (H lvar);Rewrite <- (H0 lvar); Unfold distrib;Simpl;
 Apply distrib_mult_left_correct.
Simpl;Fold AoppT;Rewrite <- (H lvar);Unfold distrib;Simpl; 
 Rewrite distrib_mult_right_correct;
 Simpl;Fold AoppT;Ring.
Save.

(**** Multiplication by the inverse product ****)

Lemma mult_eq:
  (e1,e2,a:ExprA)(lvar:(listT (prodT AT nat)))
    ~((interp_ExprA lvar a)=AzeroT)->
      (interp_ExprA lvar (EAmult a e1))=(interp_ExprA lvar (EAmult a e2))->
        (interp_ExprA lvar e1)=(interp_ExprA lvar e2).
Proof.
  Simpl;Intros;
    Apply (r_AmultT_mult (interp_ExprA lvar a) (interp_ExprA lvar e1)
      (interp_ExprA lvar e2));Assumption.
Save.

Fixpoint multiply_aux [a,e:ExprA] : ExprA :=
  Cases e of
  | (EAplus e1 e2) =>
    (EAplus (EAmult a e1) (multiply_aux a e2))
  | _ => (EAmult a e)
  end.

Definition multiply [e:ExprA] : ExprA :=
  Cases e of
  | (EAmult a e1) => (multiply_aux a e1)
  | _ => e
  end.

Lemma multiply_aux_correct:
  (a,e:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (multiply_aux a e))=
    (AmultT (interp_ExprA lvar a) (interp_ExprA lvar e)).
Proof.
Induction e;Simpl;Intros;Try (Rewrite merge_mult_correct);Auto.
  Simpl;Rewrite (H0 lvar);Ring.
Save.

Lemma multiply_correct:
  (e:ExprA)(lvar:(listT (prodT AT nat)))
    (interp_ExprA lvar (multiply e))=(interp_ExprA lvar e).
Proof.
  Induction e;Simpl;Auto.
  Intros;Apply multiply_aux_correct.
Save.

(**** Permutations and simplification ****)

Fixpoint monom_remove [a,m:ExprA] : ExprA :=
  Cases m of
  | (EAmult m0 m1) =>
    (Cases (eqExprA m0 (EAinv a)) of
     | (left _) => m1
     | (right _) => (EAmult m0 (monom_remove a m1))
     end)
  | _ =>
    (Cases (eqExprA m (EAinv a)) of
     | (left _) => EAone
     | (right _) => (EAmult a m)
     end)
  end.

Definition monom_simplif_rem := 
  Fix monom_simplif_rem {monom_simplif_rem/1:ExprA->ExprA->ExprA:=
  [a,m:ExprA] 
  Cases a of
  | (EAmult a0 a1) => (monom_simplif_rem a1 (monom_remove a0 m))
  | _ => (monom_remove a m)
  end}.

Definition monom_simplif [a,m:ExprA] : ExprA :=
  Cases m of
  | (EAmult a' m') =>
    (Cases (eqExprA a a') of
     | (left _) => (monom_simplif_rem a m')
     | (right _) => m
     end)
  | _ => m
  end.

Fixpoint inverse_simplif [a,e:ExprA] : ExprA :=
  Cases e of
  | (EAplus e1 e2) => (EAplus (monom_simplif a e1) (inverse_simplif a e2))
  | _ => (monom_simplif a e)
  end.

Lemma monom_remove_correct:(e,a:ExprA)
  (lvar:(listT (prodT AT nat)))~((interp_ExprA lvar a)=AzeroT)->
  (interp_ExprA lvar (monom_remove a e))=
  (AmultT (interp_ExprA lvar a) (interp_ExprA lvar e)).
Proof.
Induction e; Intros.
Simpl;Case (eqExprA EAzero (EAinv a));Intros;[Inversion e0|Simpl;Trivial].
Simpl;Case (eqExprA EAone (EAinv a));Intros;[Inversion e0|Simpl;Trivial].
Simpl;Case (eqExprA (EAplus e0 e1) (EAinv a));Intros;[Inversion e2|
 Simpl;Trivial].
Simpl;Case (eqExprA e0 (EAinv a));Intros.
Rewrite e2;Simpl;Fold AinvT.
Rewrite <-(AmultT_assoc (interp_ExprA lvar a) (AinvT (interp_ExprA lvar a))
             (interp_ExprA lvar e1));
  Rewrite AinvT_r;[Ring|Assumption].
Simpl;Rewrite H0;Auto; Ring.
Simpl;Fold AoppT;Case (eqExprA (EAopp e0) (EAinv a));Intros;[Inversion e1|
 Simpl;Trivial].
Unfold monom_remove;Case (eqExprA (EAinv e0) (EAinv a));Intros.
Case (eqExprA e0 a);Intros.
Rewrite e2;Simpl;Fold AinvT;Rewrite AinvT_r;Auto.
Inversion e1;Simpl;ElimType False;Auto.
Simpl;Trivial.
Unfold monom_remove;Case (eqExprA (EAvar n) (EAinv a));Intros;
 [Inversion e0|Simpl;Trivial].
Save.

Lemma monom_simplif_rem_correct:(a,e:ExprA)
  (lvar:(listT (prodT AT nat)))~((interp_ExprA lvar a)=AzeroT)->
  (interp_ExprA lvar (monom_simplif_rem a e))=
  (AmultT (interp_ExprA lvar a) (interp_ExprA lvar e)).
Proof.
Induction a;Simpl;Intros; Try Rewrite monom_remove_correct;Auto.
Elim (without_div_O_contr (interp_ExprA lvar e) 
                          (interp_ExprA lvar e0) H1);Intros.
Rewrite (H0 (monom_remove e e1) lvar H3);Rewrite monom_remove_correct;Auto.
Ring.
Save.

Lemma monom_simplif_correct:(e,a:ExprA)
  (lvar:(listT (prodT AT nat)))~((interp_ExprA lvar a)=AzeroT)->
  (interp_ExprA lvar (monom_simplif a e))=(interp_ExprA lvar e).
Proof.
Induction e;Intros;Auto.
Simpl;Case (eqExprA a e0);Intros.
Rewrite <-e2;Apply monom_simplif_rem_correct;Auto. 
Simpl;Trivial.
Save.

Lemma inverse_correct:
  (e,a:ExprA)(lvar:(listT (prodT AT nat)))~((interp_ExprA lvar a)=AzeroT)->
    (interp_ExprA lvar (inverse_simplif a e))=(interp_ExprA lvar e).
Proof.
Induction e;Intros;Auto.
Simpl;Rewrite (H0 a lvar H1); Rewrite monom_simplif_correct ; Auto.
Unfold inverse_simplif;Rewrite monom_simplif_correct ; Auto.
Save.

End Theory_of_fields.
