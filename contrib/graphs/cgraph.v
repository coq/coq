
(*s Decision procedure for arithmetic formulas by looking 
    for negative cycles in  a graph *)

Require Allmaps.
Require Arith.
Require ZArith.
Require Bool.
Require Sumbool.
Require PolyList.
Require Wf_nat.

Section ConstraintGraphs.

(*s Axiomatisation of the domain of interpretation [D] *)

  Variable D : Set.  

  Variable Dz : D.
  Variable Dplus : D -> D -> D.
  Variable Dneg : D -> D.
  Variable Dle : D -> D -> bool.

  Variable Dplus_d_z : (d:D) (Dplus d Dz)=d.
  Variable Dplus_z_d : (d:D) (Dplus Dz d)=d.
  Variable Dplus_assoc : 
   (d,d',d'':D) (Dplus (Dplus d d') d'')=(Dplus d (Dplus d' d'')).

  Variable Dplus_neg : (d:D) (Dplus d (Dneg d))=Dz.

  Variable Dle_refl : (d:D) (Dle d d)=true.
  Variable Dle_antisym : (d,d':D) (Dle d d')=true -> (Dle d' d)=true -> d=d'.
  Variable Dle_trans : 
   (d,d',d'':D) (Dle d d')=true -> (Dle d' d'')=true -> (Dle d d'')=true.
  Variable Dle_total : (d,d':D) {(Dle d d')=true}+{(Dle d' d)=true}.

  Variable Dle_plus_mono : 
   (d,d',d'',d''':D) (Dle d d')=true -> (Dle d'' d''')=true ->
      (Dle (Dplus d d'') (Dplus d' d'''))=true.

(*s Properties of [Dle] *)

Lemma Dle_true_permut : 
       (d,d':D) (Dle d d')=true -> {(Dle d' d)=false}+{d=d'}.
  Intros; Case (sumbool_of_bool (Dle d' d)); Intro; Auto.
  Save.

(*s Definition of the minimum function *)

Definition Dmin := [d,d':D] if (Dle d d') then d else d'.

Lemma Dle_true_Dmin : (d,d':D)(Dle d d')=true -> (Dmin d d')=d.
  Unfold Dmin; Intros d d' H; Rewrite H; Trivial.
  Save.

Lemma Dle_inv_Dmin : (d,d':D)(Dle d' d)=true -> (Dmin d d')=d'.
  Unfold Dmin; Intros d d' H.
  Case (sumbool_of_bool (Dle d d')); Intro H'; Rewrite H'; Auto.
  Save.

Hints Resolve Dle_true_Dmin Dle_inv_Dmin.

Lemma Dmin_idempotent : (d:D) (Dmin d d)=d.
  Proof.
    Auto.
  Qed.

Lemma Dmin_comm : (d,d':D) (Dmin d d')=(Dmin d' d).
  Proof.
    Intros d d'; Case (Dle_total d d'); Intro H. 
    Rewrite Dle_true_Dmin with 1:= H.
    Rewrite Dle_inv_Dmin with 1:= H; Trivial.
    Rewrite Dle_true_Dmin with 1:= H.
    Rewrite Dle_inv_Dmin with 1:= H; Trivial.
  Save.

Lemma Dmin_assoc 
    : (d,d',d'':D) (Dmin (Dmin d d') d'')=(Dmin d (Dmin d' d'')).
  Proof.
    Intros d d' d''; Case (Dle_total d d'); Intro H.
    Rewrite Dle_true_Dmin with 1:= H.
    Case (Dle_total d' d''); Intro H'.
    Rewrite Dle_true_Dmin with 1:= H'.
    Rewrite Dle_true_Dmin with 1:= H.
    Rewrite (Dle_true_Dmin d d''); EAuto.
    Rewrite Dle_inv_Dmin with 1:= H'; Trivial.
    Rewrite Dle_inv_Dmin with 1:= H.
    Case (Dle_total d' d''); Intro H'.
    Rewrite Dle_true_Dmin with 1:= H'.
    Rewrite Dle_inv_Dmin with 1:= H; Trivial.
    Rewrite Dle_inv_Dmin with 1:= H'.
    Rewrite (Dle_inv_Dmin d d''); EAuto.
Save.

Lemma Dmin_le_1 : (d,d':D) (Dle (Dmin d d') d)=true.
  Proof.
    Intros. Case (Dle_total d d'); Intro H.
    Rewrite Dle_true_Dmin with 1:= H; Auto.
    Rewrite Dle_inv_Dmin with 1:= H; Auto.
  Qed.

Lemma Dmin_le_2 : (d,d':D) (Dle (Dmin d d') d')=true.
  Proof.
    Intros. Rewrite (Dmin_comm d d'). Apply Dmin_le_1.
  Qed.

Lemma Dmin_le_3 : (d,d',d'':D) (Dle d (Dmin d' d''))=true -> (Dle d d')=true.
  Proof.
    Intros d d' d''; Elim (Dle_total d' d''); Intro H0.
    Rewrite Dle_true_Dmin with 1:=H0; Trivial.
    Rewrite Dle_inv_Dmin with 1:=H0; EAuto.
  Qed.

Lemma Dmin_le_4 : (d,d',d'':D) (Dle d (Dmin d' d''))=true -> (Dle d d'')=true.
  Proof.
    Intros. Rewrite (Dmin_comm d' d'') in H. Exact (Dmin_le_3 ? ? ? H).
  Qed.

Lemma Dmin_le_5 : (d,d',d'':D) (Dle d d')=true -> (Dle d d'')=true ->
      (Dle d (Dmin d' d''))=true.
  Proof.
    Intros. Unfold Dmin. Case (Dle d' d''); Assumption.
  Qed.

(*s Properties of [Dneg] *)

Lemma Dneg_Dz : (Dneg Dz)=Dz.
  Proof.
    Rewrite <- (Dplus_z_d (Dneg Dz)). Apply Dplus_neg.
  Qed.

Lemma Dneg_neg : (d:D) (Dneg (Dneg d))=d.
  Proof.
    Intro. Rewrite <- (Dplus_z_d (Dneg (Dneg d))). Rewrite <- (Dplus_neg d).
    Rewrite Dplus_assoc. Rewrite Dplus_neg. Apply Dplus_d_z.
  Qed.

Lemma Dplus_neg_2 : (d:D) (Dplus (Dneg d) d)=Dz.
  Proof.
    Intro. Cut (Dplus (Dneg d) (Dneg (Dneg d)))=Dz. Rewrite Dneg_neg. Trivial.
    Apply Dplus_neg.
  Qed.

(*s Properties of [Dplus] *)

Lemma Dplus_reg_l 
   : (d,d',d'':D) (Dle (Dplus d'' d) (Dplus d'' d'))=true 
               -> (Dle d d')=true.
  Proof.
    Intros. Rewrite <- (Dplus_z_d d). Rewrite <- (Dplus_z_d d'). Rewrite <- (Dplus_neg_2 d'').
    Rewrite (Dplus_assoc (Dneg d'') d'' d). Rewrite (Dplus_assoc (Dneg d'') d'' d').
    Apply Dle_plus_mono. Apply Dle_refl.
    Assumption.
  Qed.

Lemma Dplus_reg_r 
   : (d,d',d'':D) (Dle (Dplus d d'') (Dplus d' d''))=true -> (Dle d d')=true.
  Proof.
    Intros. Rewrite <- (Dplus_d_z d). Rewrite <- (Dplus_d_z d'). Rewrite <- (Dplus_neg d'').
    Rewrite <- (Dplus_assoc d d'' (Dneg d'')). Rewrite <- (Dplus_assoc d' d'' (Dneg d'')).
    Apply Dle_plus_mono. Assumption.
    Apply Dle_refl.
  Qed.

Lemma Dmin_plus_l 
   : (d,d',d'':D) (Dplus (Dmin d d') d'')=(Dmin (Dplus d d'') (Dplus d' d'')).
  Proof.
    Intros d d' d''; Case (Dle_total d d'); Intro H.
    Rewrite Dle_true_Dmin with 1:=H.
    Rewrite (Dle_true_Dmin (Dplus d d'')); Auto.
    Rewrite Dle_inv_Dmin with 1:=H.
    Rewrite (Dle_inv_Dmin (Dplus d d'')); Auto.
  Qed.

Lemma Dmin_plus_r 
   : (d,d',d'':D) (Dplus d'' (Dmin d d'))=(Dmin (Dplus d'' d) (Dplus d'' d')).
  Proof.
   Intros d d' d''; Case (Dle_total d d'); Intro H.
    Rewrite Dle_true_Dmin with 1:=H.
    Rewrite (Dle_true_Dmin (Dplus d'' d)); Auto.
    Rewrite Dle_inv_Dmin with 1:=H.
    Rewrite (Dle_inv_Dmin (Dplus d'' d)); Auto.
  Qed.

Lemma Dle_neg : (d:D) (Dle Dz d)=true -> (Dle (Dneg d) Dz)=true.
  Proof.
    Intros. Cut (Dle (Dplus Dz (Dneg d)) (Dplus d (Dneg d)))=true. Intro.
    Rewrite (Dplus_z_d (Dneg d)) in H0. Rewrite (Dplus_neg d) in H0. Assumption.
    Exact (Dle_plus_mono ? ? ? ? H (Dle_refl ?)).
  Qed.

Lemma Dle_neg_2 : (d:D) (Dle d Dz)=true -> (Dle Dz (Dneg d))=true.
  Proof.
    Intros. Cut (Dle (Dplus d (Dneg d)) (Dplus Dz (Dneg d)))=true. Intro.
    Rewrite (Dplus_neg d) in H0. Rewrite (Dplus_z_d (Dneg d)) in H0. Assumption.
    Exact (Dle_plus_mono ? ? ? ? H (Dle_refl ?)).
  Qed.
 
Lemma Dnotle_not_eq : (d,d':D)(Dle d d')=false ->~d=d'.
  Red; Intros.
  Apply diff_true_false.
  Rewrite H0 in H.  
  Rewrite (Dle_refl d') in H; Trivial.
  Save.

Hints Immediate Dnotle_not_eq.

Lemma Dnotle_not_eq_sym : (d,d':D) (Dle d d')=false -> ~d'=d.
  Proof.
    Intros; Apply sym_not_eq; Auto.
  Qed.

Hints Immediate Dnotle_not_eq_sym.

(*s Equality on [D] is decidable *)

Lemma D_dec : (d,d':D) {d=d'}+{~d=d'}.
  Proof.
    Intros d d'; Case (sumbool_of_bool (Dle d d')); Intro H; Auto. 
    Case (sumbool_of_bool (Dle d' d)); Intro H0; Auto.
  Qed.

Lemma Dnotle_3_cases 
  : (d,d':D) {(Dle d d')=false}+{d=d'}+{(Dle d' d)=false}.
  Proof.
   Intros d d'; Case (sumbool_of_bool (Dle d d')); Intro H; Auto. 
    Case (sumbool_of_bool (Dle d' d)); Intro H0; Auto.
  Qed.

Lemma Dle_noteq_notle 
   : (d,d':D) (Dle d' d)=true -> ~d=d' -> (Dle d d')=false.
  Proof.
    Intros d d'; Case (sumbool_of_bool (Dle d d')); Intro H; Auto. 
    Intros; Absurd d=d'; Auto.
  Qed.

Lemma Dnotle_not_refl 
   : (d:D) ~(Dle d d)=false.
  Proof.
    Red; Intro;  Rewrite (Dle_refl d).
    Exact diff_true_false.
  Qed.


Lemma Dnotle_elim : 
  (d,d':D) (Dle d' d)=false -> ((Dle d d')=true /\ ~d=d').
  Intros.
  Case (Dle_total d d'); Intro H'; Auto.
  Case diff_true_false.
  Rewrite <- H'; Trivial.
Save.  

Lemma Dnotle_trans : (d,d',d'':D) (Dle d d')=false -> (Dle d' d'')=false -> (Dle d d'')=false.
  Proof.
   Intros.
   Case Dnotle_elim with 1:= H; Intros.
   Case Dnotle_elim with 1:= H0; Intros.
   Apply Dle_noteq_notle; EAuto.
   Red; Intros.
   Apply diff_false_true.
   Rewrite <- H0.
   Rewrite <- H5; Trivial.
   Save.

Lemma Dnotle_le_1 : (d,d':D) (Dle d d')=false -> (Dle d' d)=true.
  Proof.
    Intros; Case Dnotle_elim with 1:= H; Trivial.
  Qed.

Lemma Dmin_le_distr_l : (d,d',d'':D) (Dle (Dmin d d') d'')=(orb (Dle d d'') (Dle d' d'')).
  Proof.
    Intros; Case (Dle_total d d'); Intro H.
    Rewrite Dle_true_Dmin with 1:= H.
    Pattern (Dle d d''); Apply bool_eq_ind; Intro H'; Simpl; Trivial.
    Pattern (Dle d' d''); Apply bool_eq_ind; Intro H''; Simpl; Trivial.
    Rewrite <- H'; EAuto.
    Rewrite Dle_inv_Dmin with 1:= H.
    Pattern (Dle d d''); Apply bool_eq_ind; Intro H'; Simpl; EAuto.
    Save.

Lemma Dmin_choice : (d,d':D) {(Dmin d d')=d}+{(Dmin d d')=d'}.
  Proof.
    Unfold Dmin. Intros. Elim (sumbool_of_bool (Dle d d')). Intro H. Left . Rewrite H. Reflexivity.
    Intro H. Right . Rewrite H. Reflexivity.
  Qed.

Lemma Dnotle_noteq : (d,d':D) (Dle d d')=false -> ~d=d'.
  Proof.
    Unfold not. Intros. Rewrite H0 in H. Rewrite (Dle_refl d') in H. Discriminate H.
  Qed.

Lemma Dneg_plus : (d,d':D) (Dneg (Dplus d d'))=(Dplus (Dneg d') (Dneg d)).
  Proof.
    Intros. Cut (Dplus (Dplus d d') (Dplus (Dneg d') (Dneg d)))=Dz. Intro.
    Rewrite <- (Dplus_d_z (Dneg (Dplus d d'))). Rewrite <- H. Rewrite <- Dplus_assoc.
    Rewrite Dplus_neg_2. Rewrite Dplus_z_d. Reflexivity.
    Rewrite Dplus_assoc. Rewrite <- (Dplus_assoc d' (Dneg d') (Dneg d)). Rewrite Dplus_neg.
    Rewrite Dplus_z_d. Apply Dplus_neg.
  Qed.

Lemma Dneg_le : (d,d':D) (Dle d d')=true -> (Dle (Dneg d') (Dneg d))=true.
  Proof.
    Intros. Apply Dplus_reg_l with d'':=d'. Rewrite Dplus_neg. Rewrite <- (Dneg_neg d').
    Rewrite <- Dneg_plus. Apply Dle_neg_2. Rewrite <- (Dplus_neg d').
    Exact (Dle_plus_mono ? ? ? ? H (Dle_refl ?)).
  Qed.

Lemma Dnotle_plus_mono_1 : (d,d',d'',d''':D) (Dle d' d)=true -> (Dle d'' d''')=false
      	  -> (Dle (Dplus d d'') (Dplus d' d'''))=false.
  Proof.
    Intros. Apply Dle_noteq_notle. Apply Dle_plus_mono. Assumption.
    Apply Dnotle_le_1. Assumption.
    Unfold not. Intro H1.
    Cut (Dle (Dplus (Dneg d) (Dplus d d'')) (Dplus (Dneg d') (Dplus d' d''')))=true.
    Rewrite <- (Dplus_assoc (Dneg d) d d''). Rewrite Dplus_neg_2. Rewrite Dplus_z_d.
    Rewrite <- Dplus_assoc. Rewrite Dplus_neg_2. Rewrite Dplus_z_d. Rewrite H0.
    Intro H2. Discriminate H2.
    Apply Dle_plus_mono. Apply Dneg_le. Assumption.
    Rewrite H1. Apply Dle_refl.
  Qed.

Lemma Dnotle_plus_mono : (d,d',d'',d''':D) (Dle d d')=false -> (Dle d'' d''')=false
      	  -> (Dle (Dplus d d'') (Dplus d' d'''))=false.
  Proof.
    Intros. (Apply Dnotle_plus_mono_1; Try Assumption). (Apply Dnotle_le_1; Assumption).
  Qed.

(*s Extending D with an element NONE representing infinity *)

Definition Ddmin := [dd,dd':(option D)] Cases dd dd' of
                                              NONE _ => dd'
					    | _ NONE => dd
					    | (SOME d) (SOME d') => (SOME D (Dmin d d'))
					  end.

Lemma Ddmin_idempotent : (dd:(option D)) (Ddmin dd dd)=dd.
  Proof.
    Induction dd. Trivial.
    Intro. Simpl. Rewrite Dmin_idempotent. Reflexivity.
  Qed.

Lemma Ddmin_comm : (dd,dd':(option D)) (Ddmin dd dd')=(Ddmin dd' dd).
  Proof.
    Induction dd. Intro. (Case dd'; Reflexivity).
    Intro d. Induction dd'. Reflexivity.
    Intro d'. Simpl. Rewrite Dmin_comm. Reflexivity.
  Qed.

Lemma Ddmin_assoc : (dd,dd',dd'':(option D))
      (Ddmin (Ddmin dd dd') dd'')=(Ddmin dd (Ddmin dd' dd'')).
  Proof.
    Intros. Case dd. Simpl. Case dd'. Simpl. (Case dd''; Reflexivity).
    Intro. Simpl. (Case dd''; Reflexivity).
    Intro. Simpl. Case dd'. Simpl. (Case dd''; Reflexivity).
    Intro d'. Simpl. Case dd''. Reflexivity.
    Intro d''. Rewrite Dmin_assoc. Reflexivity.
  Qed.

(*s The order [Dle] extended to $D_{\infty}$ *)
Definition Ddle 
  := [dd,dd':(option D)] Cases dd dd' of
                               _ NONE => true
			  | NONE _    => false
                          | (SOME d) (SOME d') => (Dle d d')
		         end.

Lemma Ddle_refl : (dd:(option D)) (Ddle dd dd)=true.
  Proof.
    Intro. Case dd. Reflexivity.
    Intro. Exact (Dle_refl d).
  Qed.

Lemma Ddle_antisym 
  : (dd,dd':(option D)) (Ddle dd dd')=true -> (Ddle dd' dd)=true -> dd=dd'.
  Proof.
    Intros dd dd'. Case dd. Case dd'. Trivial.
    Intros. Discriminate H.
    Case dd'. Intros. Discriminate H0.
    Intros. Rewrite (Dle_antisym ? ? H0 H). Reflexivity.
  Qed.

Lemma Ddle_trans 
  : (dd,dd',dd'':(option D)) 
    (Ddle dd dd')=true -> (Ddle dd' dd'')=true -> (Ddle dd dd'')=true.
  Proof.
    Intros dd dd' dd''. Case dd''. (Case dd; Trivial).
    Intro d''. Case dd'. Intros. Discriminate H0.
    Intro d'. Case dd. Intro. Discriminate H.
    Intros d H H0. Exact (Dle_trans ? ? ? H H0).
  Qed.

Lemma Ddle_d_none : (dd:(option D)) (Ddle dd (NONE D))=true.
  Proof.
    Induction dd; Trivial.
  Qed.

Lemma Ddmin_le_1 : (dd,dd':(option D)) (Ddle (Ddmin dd dd') dd)=true.
  Proof.
    Intros. Case dd. (Case dd'; Reflexivity).
    Intro d. Case dd'. Apply Ddle_refl.
    Exact (Dmin_le_1 d).
  Qed.

Lemma Ddmin_le_2 : (dd,dd':(option D)) (Ddle (Ddmin dd dd') dd')=true.
  Proof.
    Intros. Rewrite (Ddmin_comm dd dd'). Apply Ddmin_le_1.
  Qed.

Lemma Ddmin_le_3 
  : (dd,dd',dd'':(option D)) 
    (Ddle dd (Ddmin dd' dd''))=true -> (Ddle dd dd')=true.
  Proof.
    Intros dd dd' dd''. Case dd'. (Case dd; Trivial).
    Intro d'. Case dd. Case dd''. Intro. Discriminate H.
    Intros d'' H. Discriminate H.
    Intro d. Case dd''. Trivial.
    Exact (Dmin_le_3 d d').
  Qed.

Lemma Ddmin_le_4 : (dd,dd',dd'':(option D)) (Ddle dd (Ddmin dd' dd''))=true ->
      (Ddle dd dd'')=true.
  Proof.
    Intros. Rewrite (Ddmin_comm dd' dd'') in H. Exact (Ddmin_le_3 ? ? ? H).
  Qed.

Lemma Ddmin_le_distr_l 
  : (dd,dd',dd'':(option D))
    (Ddle (Ddmin dd dd') dd'')=(orb (Ddle dd dd'') (Ddle dd' dd'')).
  Proof.
    Induction dd. Induction dd'. (Induction dd''; Trivial).
    Intro d. (Induction dd''; Trivial).
    Intro d. Induction dd'. (Induction dd''; Trivial).
    Simpl. Intro d'. Rewrite orb_b_false. Reflexivity.
    Intro d'. (Induction dd''; Trivial). Simpl. Exact (Dmin_le_distr_l d d').
  Qed.

Lemma Ddmin_choice 
  : (dd,dd':(option D)) {(Ddmin dd dd')=dd}+{(Ddmin dd dd')=dd'}.
  Proof.
    Induction dd. Intro. Right . Simpl. (Case dd'; Reflexivity).
    Intro d. Induction dd'. Left . Reflexivity.
    Intro d'. Simpl. Elim (Dmin_choice d d'). Intro H. Left . Rewrite H. Reflexivity.
    Intro H. Right . Rewrite H. Reflexivity.
  Qed.

(*s Operation [Ddplus] on $D_{\infty}$ *)

Definition Ddplus := [dd:(option D)][d':D]
      Cases dd of
          (SOME d) => (SOME ? (Dplus d d'))
	| _ => dd
      end.

Lemma Ddmin_plus_l 
  : (dd,dd':(option D)) (d'':D)
    (Ddplus (Ddmin dd dd') d'')=(Ddmin (Ddplus dd d'') (Ddplus dd' d'')).
  Proof.
    Induction dd. Induction dd'. Trivial.
    Trivial.
    Intro d. Induction dd'. Trivial.
    Intros d' d''. Simpl. Rewrite Dmin_plus_l. Reflexivity.
  Qed.

Lemma Ddle_plus_mono 
  : (dd,dd':(option D)) (d,d':D)
    (Ddle dd dd')=true -> (Dle d d')=true ->
        (Ddle (Ddplus dd d) (Ddplus dd' d'))=true.
  Proof.
    Induction dd. Induction dd'. Intros. Trivial.
    Simpl. Intros. Assumption.
    Intro d0. Induction dd'. Trivial.
    Simpl. Exact (Dle_plus_mono d0).
  Qed.

Lemma Ddplus_reg_r 
  : (dd,dd':(option D)) (d'':D)
        (Ddle (Ddplus dd d'') (Ddplus dd' d''))=true->(Ddle dd dd')=true.
  Proof.
    Induction dd. Induction dd'. Trivial.
    Simpl. Trivial.
    Intro d. Induction dd'. Trivial.
    Intros d' d'' H. Exact (Dplus_reg_r d d' d'' H).
  Qed.

(*s Introducing graphs of objects in [D] *)

Definition CGraph1 := (Map (Map D)).

Definition CGraph := (option CGraph1).

Section CGDist.

    Variable cg : CGraph1.

Definition CG_edge := [x,y:ad]
      	Cases (MapGet ? cg x) of
	    (SOME edges) => Cases (MapGet ? edges y) of
                                (SOME d) => (SOME D d)
		              | _ => (NONE D)
			    end
          | _ => (NONE D)
        end.

(*s Let $\rho$ be an interpretation of adresses as elements in [D], 
    the graph [cg] is satisfied by $\rho$ if for any edge 
    from $x$ to $y$ indexed by $d$, we have $\rho(x) \leq \rho(y)+d$
   A graph is consistent if there exists an interpretation which satisfies it.
*)

Definition CGsat 
  := [rho:ad->D] 
     (x,y:ad) (d:D)
     (CG_edge x y)=(SOME D d) -> (Dle (rho x) (Dplus (rho y) d))=true.


Definition CGconsistent := (sig ? CGsat). 

(* [CG_path last d l] if there exists a path starting from [last] with successive 
   vertexes $l=[x0;...;xn]$ $(xn=last)$ and [d] is the sum of the weights on the 
   edges *)

Inductive CG_path [last : ad] : D -> (list ad) -> Set :=
        CG_p1 : (x:ad) x=last -> (CG_path last Dz (cons x (nil ?)))
      | CG_p2 : (x,y:ad) (l:(list ad)) (d:D) (CG_path last d (cons y l)) ->
      	          (d':D) (CG_edge x y)=(SOME D d') ->
                    (CG_path last (Dplus d d') (cons x (cons y l))).

(* If $\rho$ satisfies the graph and there is a path from [last] to [x] of 
   weight d then $\rho(x) \leq \rho(last)+d$
*)

Definition first : (list ad) -> ad := [l]Cases l of nil => ad_z | (cons x _) => x end.

Lemma CG_path_head 
  : (l:(list ad)) (last:ad) (d:D) (CG_path last d l) ->
      	(rho:ad->D) (CGsat rho) -> (Dle (rho (first l)) (Dplus (rho last) d))=true.
    Proof.
    Intros; Elim H; Simpl; Intros.
    Rewrite e; Rewrite Dplus_d_z; Auto.
    Apply Dle_trans with (Dplus (rho y) d'); Auto.
    Rewrite <- Dplus_assoc; Auto.
    Save.

Lemma CG_path_correct 
  : (l:(list ad)) (x,last:ad) (d:D) (CG_path last d (cons x l)) ->
      	(rho:ad->D) (CGsat rho) -> (Dle (rho x) (Dplus (rho last) d))=true.
    Proof.
    Intros; Apply (CG_path_head (cons x l) last d); Trivial.
    Save.

(*s If there is a circuit [(cons x l)] with negative weight [d], then [cg] is inconsistent: *)

Theorem CG_circuit_correct 
  : (x:ad) (d:D) (l:(list ad))
    (CG_path x d (cons x l)) -> (Dle Dz d)=false -> CGconsistent -> False.
    Proof.
      Intros. Unfold CGconsistent in H1. Elim H1. Intros rho H2.
      Cut (Dle (Dplus (rho x) Dz) (Dplus (rho x) d))=true. Intro H3.
      Rewrite (Dplus_reg_l ? ? ? H3) in H0. Discriminate H0.
      Rewrite Dplus_d_z. Exact (CG_path_correct l x x d H rho H2).
    Qed.

Section CGConsistent.

      Variable P : CGconsistent.

(*s Assuming that [cg] is consistent, we can build a distance d(x,y) as follows:
      	 d(x,y) is the length of the shortest path from x to y (or +infty if none). *)

Lemma CG_circuits_non_negative_weight 
  : (x:ad) (d:D) (l:(list ad)) (CG_path x d (cons x l)) -> (Dle Dz d)=true.
      Proof.
      	Intros. Elim (sumbool_of_bool (Dle Dz d)). Trivial.
	Intro H0. Elim (CG_circuit_correct x d l H H0 P).
      Qed.

End CGConsistent.

(*s We assume that any cycle has a positive weight *)

Section CGNoBadCycles.

      Variable no_bad_cycles : (x:ad) (d:D) (l:(list ad))
      	 (CG_path x d (cons x l)) -> (Dle Dz d)=true.

(*s The edges are in the domain of the graph *)

Lemma CG_edge_in_cg_1 
  : (x,y:ad) (d:D) (CG_edge x y)=(SOME D d) -> (in_FSet x (MapDom ? cg))=true.
      Proof.
      	Unfold CG_edge. Intros x y d. 
	Elim (option_sum ? (MapGet (Map D) cg x)). Intro H.
      	Elim H. Intros edges H0. Rewrite H0. Intros. 
	Exact (MapDom_semantics_1 ? cg x edges H0).
	Intros H H0. Rewrite H in H0. Discriminate H0.
      Qed.


(*s The elements of a path are in the domain of the graph extended with 
    the last element *)
Lemma CG_path_in_cg_1 
  : (l:(list ad)) (last:ad) (d:D)
    (CG_path last d l) -> (MapSubset ? ? (Elems l)
                                 (MapPut ? (MapDom ? cg) last tt)).
      Proof.
      
      	Induction 1.
        Unfold MapSubset; Unfold Elems; Simpl; Intros.
        Rewrite in_dom_put.
        Rewrite in_dom_M1 in H0.
        Rewrite <- e.
        Rewrite (ad_eq_comm a x).
        Rewrite H0; Simpl; Trivial.
        Unfold MapSubset.
        Intros; Rewrite in_dom_put.
        Change (in_dom unit a 
                 (MapPut unit (Elems (cons y l0)) x tt))=true in H1.
        Rewrite in_dom_put in H1.
        Case orb_prop with 1:=H1; Intro.
      	Rewrite (ad_eq_complete ? ? H2).
        Change 
         (orb (ad_eq x last) (in_FSet x (MapDom (Map D) cg)))=true.
	Rewrite CG_edge_in_cg_1 with 1:=e; Auto with bool.
        LetTac H3:=(H0 a H2).
	Rewrite in_dom_put in H3.
	Trivial.
Save.

Lemma CG_path_last 
  : (l:(list ad)) (last:ad) (d:D)
    (CG_path last d l) -> {l':(list ad) | l=(app l' (cons last (nil ad)))}.
      Proof.
      	Induction 1; Intros. 
        Exists (nil ad); Simpl; Rewrite e; Trivial.
	Case H0; Intros l' H1.
        Exists (cons x l'); Simpl.
        Rewrite H1; Auto.
      Qed.

(*s The length of a path without repetition is less than the
   cardinal of the map representing the graph *)

Lemma ad_simple_path_bounded_card 
  : (l:(list ad)) (last,x:ad) (d:D)
    (CG_path last d (cons x l)) -> (ad_list_stutters (cons x l))=false
	    -> (le (length (cons x l)) (S (MapCard ? cg))).
      Proof.
      	Intros. Apply le_trans with m:=(MapCard ? (MapPut ? (MapDom ? cg) last tt)).
      	Rewrite (ad_list_not_stutters_card (cons x l) H0). Apply MapSubset_Card_le.
      	Apply CG_path_in_cg_1 with 1:=H; Trivial.
	Rewrite (MapCard_Dom ? cg). Apply MapCard_Put_ub.
      Qed.

Lemma CG_path_app_1 : (l1,l2:(list ad)) (last,x:ad) (d1,d2:D)
      	  (CG_path last d2 (cons x l2)) -> (CG_path x d1 l1) ->
	    (CG_path last (Dplus d2 d1) (app l1 l2)).
      Proof.
        Intros.
        Elim H0; Intros.
        Simpl; Rewrite Dplus_d_z; Rewrite e; Trivial.
        Rewrite <- Dplus_assoc.
        Simpl; Constructor; Auto.
      Save.

Lemma CG_path_app_2 : (l1,l2:(list ad)) (last,x:ad) (d:D)
      	  (CG_path last d (app l1 (cons x l2))) ->
	    {d2 : D & (CG_path last d2 (cons x l2))}.
      Proof.
      	Induction l1. Simpl. Intros. Split with d. Assumption.
	Simpl. Induction l. Intros. Simpl in H0. Inversion H0. Split with d0. Assumption.
	Intros. Simpl in H1. Inversion H1. Exact (H0 l2 last x d0 H5).
      Qed.

Lemma CG_path_app_3 : (l1,l2:(list ad)) (last,x:ad) (d:D)
      	  (CG_path last d (app l1 (cons x l2))) ->
	    {d1 : D & (CG_path x d1 (app l1 (cons x (nil ad))))}.
      Proof.
      	Induction l1. Simpl. Intros. Split with Dz. Apply CG_p1. Reflexivity.
	Induction l. Simpl. Intros. Inversion H0. Split with d'. Rewrite <- (Dplus_z_d d').
      	Apply CG_p2. Apply CG_p1. Reflexivity.
	Assumption.
	Simpl. Intros. Inversion H1. Elim (H0 ? ? ? ? H5). Intros d1 H9. Split with (Dplus d1 d').
      	Apply CG_p2. Assumption.
	Assumption.
      Qed.

Lemma CG_path_weight_and_last_unique 
  : (l:(list ad)) (last,last':ad) (d,d':D)
    (CG_path last d l) -> (CG_path last' d' l) -> d=d' /\ last=last'.
      Proof.
        Intros l last last' d d' H; Generalize d'.
      	Elim H; Intros. 
	Inversion H0. 
	Split; Trivial. Transitivity x; Auto.
        Inversion H1.
        Case H0 with 1:=H5; Split; Intros; Trivial.
        Rewrite H8.
        Replace d'0 with d'2; Auto.
        Cut (SOME D d'2)=(SOME D d'0).
        Intro E; Injection E; Trivial.
        Transitivity (CG_edge x y); Auto.
      Qed.

    Inductive and_sp [A:Set; B:Prop] : Set := conj_sp : A -> B -> (and_sp A B).

(*s Given a path, one may find a shortest path withour repetition *)

Lemma ad_path_then_simple_path : 
          (l:(list ad)) (last:ad) (d:D)
      	  (CG_path last d l) ->
	    {sl:(list ad) & {d0:D & 
                   (and_sp (CG_path last d0 (cons (first l) sl))
                           ((ad_list_stutters (cons (first l) sl))=false /\
				              (Dle d0 d)=true))}}.
      Proof.
      	Induction 1; Unfold first; Intros.
        Exists (nil ad); Exists Dz; Split; Auto.
        Constructor; Auto.
        Case H0; Clear H0; Intros sl (d1,(H1,(H2,H3))).
        Elim (sumbool_of_bool (ad_in_list x (cons y sl))); Intro.
        Case (ad_in_list_forms_circuit x (cons y sl) a); Intros.
        Case s; Clear a s; Intros l2 H4.
        Case (CG_path_app_2 x0 l2 last x d1).
        Rewrite <- H4; Trivial.
        Intros d2 H5; Exists l2; Exists d2.
        Split; Trivial.
        Split.
        Apply (ad_list_stutters_app_conv_r x0).
	Rewrite <- H4; Trivial.
        Apply Dle_trans with (Dplus d1 d').
	Case (CG_path_app_3 (cons x x0) l2 last x (Dplus d1 d')).
        Simpl; Rewrite <- H4; Constructor; Trivial.
        Intros d3 H6.
        Replace (Dplus d1 d') with (Dplus d2 d3).
        Apply Dle_trans with (Dplus d2 Dz).
        Rewrite Dplus_d_z; Auto.
        Apply Dle_plus_mono; Trivial.
        Apply (no_bad_cycles x d3 (app x0 (cons x (nil ad)))); Auto.
        Case (CG_path_weight_and_last_unique 
                (app (app (cons x x0) (cons x (nil ad))) l2) 
                last last (Dplus d2 d3) (Dplus d1 d')); Auto.
        Apply CG_path_app_1 with x; Trivial.
        Replace (app (app (cons x x0) (cons x (nil ad))) l2)
        with (cons x (cons y sl)); Auto.
        Constructor; Auto.
        Rewrite H4; Rewrite <- ass_app; Simpl; Trivial.
        Apply Dle_plus_mono; Trivial.
	Exists (cons y sl); Exists (Dplus d1 d'); Repeat Split; Auto.
        Constructor; Auto.
        Change (orb (ad_in_list x (cons y sl)) (ad_list_stutters (cons y sl))) = false.
        Apply orb_false_intro; Trivial.
      Qed.

Lemma CG_path_app_4 : (l1,l2:(list ad)) (last,x:ad) (d:D)
      	  (CG_path last d (app l1 (cons x l2))) ->
	    {d1 : D & {d2 : D &
	          (and_sp (CG_path x d1 (app l1 (cons x (nil ad)))) *
		          (CG_path last d2 (cons x l2))
			  d=(Dplus d2 d1))}}.
      Proof.
      	Intros. Elim (CG_path_app_2 l1 l2 last x d). Intros d1 H0.
      	Elim (CG_path_app_3 l1 l2 last x d). Intros d2 H1. Split with d2. Split with d1.
      	Split. Exact (H1,H0).
	Cut (app l1 (cons x l2))=(app (app l1 (cons x (nil ad))) l2). 
	Intro. Rewrite H2 in H.
      	Elim (CG_path_weight_and_last_unique ? ? ? ? ? H
               (CG_path_app_1 (app l1 (cons x (nil ad))) l2 last x d2 d1 H0 H1)).
      	Trivial.
	Exact (ass_app l1 (cons x (nil ad)) l2).
	Assumption.
	Assumption.
      Qed.

(*s [(ad_simple_path_naive_search x y prefix n)] is true when 
    there esists a path [x::l] from [y] to [x] of length less than 
    [n] with edges not in prefix
*)

Fixpoint ad_simple_path_naive_search [x,y:ad; l:(list ad); n:nat] : bool :=
        (orb (ad_eq x y)
      	Cases n of
	    O => false
	  | (S n') => Cases (MapGet ? cg x) of
	                  NONE => false
			| (SOME edges) =>
                          let l'=(cons x l) in (* builds reverse path *)
                          Cases (MapSweep D
			           [z:ad][d:D] if (ad_in_list z l')
                                               then false
				               else (ad_simple_path_naive_search z y l' n')
				   edges) of
			      NONE => false
			    | (SOME _) => true
			  end
                     end
        end).

Lemma ad_simple_path_naive_search_correct_1 
  : (n:nat) (x,y:ad) (l:(list ad)) (d:D)
    (le (length l) n) -> (CG_path y d (cons x l)) ->
    (prefix:(list ad))
      	    (ad_list_stutters (app (rev prefix) (cons x l)))=false ->
	    (ad_simple_path_naive_search x y prefix n)=true.
      Proof.
      	Induction n. Intros x y l. Case l. Intros. Inversion H0. 
        Rewrite H4. Simpl.
      	Rewrite (ad_eq_correct y). Reflexivity.
	Intros. Elim (le_Sn_O ? H).
	Intros n0 H x y l. Case l. Intros. Inversion H1. Rewrite H5. Simpl.
      	Rewrite (ad_eq_correct y). Reflexivity.
	Intros. Simpl. Elim (sumbool_of_bool (ad_eq x y)). Intro H3. Rewrite H3. Reflexivity.
	Intro H3. Rewrite H3. Simpl. Elim (option_sum ? (MapGet ? cg x)). Intro H4. Elim H4.
      	Clear H4. Intros edges H4. Rewrite H4. Inversion_clear H1. Unfold CG_edge in H6.
      	Rewrite H4 in H6. Elim (option_sum ? (MapGet D edges a)). Intro H7. Elim H7. Clear H7.
      	Intros d'' H7. Rewrite H7 in H6.
      	Cut (if (ad_in_list a (cons x prefix))
             then false
             else (ad_simple_path_naive_search a y (cons x prefix) n0))=true.
      	Intro. Elim (MapSweep_semantics_4 D [z:ad] [_:D]
         (if (orb (ad_eq z x) (ad_in_list z prefix))
          then false
          else (ad_simple_path_naive_search z y (cons x prefix) n0))
             edges a d'' H7 H1).
      	Intros a' H8. Elim H8. Intros d1 H9. Rewrite H9. Reflexivity.
	Rewrite (ad_list_app_rev prefix (cons a l0) x) in H2.
      	Rewrite <- (ad_in_list_rev (cons x prefix) a).
      	Rewrite (ad_list_stutters_prev_conv_l ? ? ? H2).
      	Exact (H a y l0 d0 (le_S_n ? ? H0) H5 (cons x prefix) H2).
	Intro H7. Rewrite H7 in H6. Discriminate H6.
	Intro H4. Inversion_clear H1. Unfold CG_edge in H6. Rewrite H4 in H6. Discriminate H6.
      Qed.

Lemma ad_simple_path_naive_search_correct 
  : (n:nat) (x,y:ad) (l:(list ad)) (d:D)
    (le (length l) n) -> (CG_path y d (cons x l)) 
    -> (ad_list_stutters (cons x l))=false 
    -> (ad_simple_path_naive_search x y (nil ad) n)=true.
      Proof.
      	Intros. Exact (ad_simple_path_naive_search_correct_1 n x y l d H H0 (nil ad) H1).
      Qed.

Lemma ad_simple_path_naive_search_complete_1 
  : (n:nat) (x,y:ad) (prefix:(list ad))
    (d':D) (CG_path x d' (rev (cons x prefix))) ->
      	   (ad_list_stutters (cons x prefix))=false ->
      	   (ad_simple_path_naive_search x y prefix n)=true ->
	     {d:D & {l:(list ad) & (and_sp (CG_path y d (app (rev (cons x prefix)) l))
	                                   (ad_list_stutters (app (rev (cons x prefix)) l))
                                                =false)}}.
      Proof.
      	Induction n. Intros. Split with d'. Split with (nil ad). Simpl in H1.
      	Rewrite (orb_b_false (ad_eq x y)) in H1. Rewrite <- (ad_eq_complete ? ? H1).
      	Rewrite <- app_nil_end. Split. Assumption.
	Rewrite ad_list_stutters_rev. Assumption.
	Intros. Simpl in H2. Elim (orb_true_elim ? ? H2). Intro H3.
      	Rewrite <- (ad_eq_complete ? ? H3). Split with d'. Split with (nil ad).
      	Rewrite <- app_nil_end. Split. Assumption.
	Rewrite ad_list_stutters_rev. Assumption.
	Intro H3. Clear H2. Elim (option_sum ? (MapGet ? cg x)). Intro H4. Elim H4.
      	Intros edges H5. Rewrite H5 in H3.
      	Elim (option_sum ? (MapSweep D [z:ad] [_:D]
                            (if (orb (ad_eq z x) (ad_in_list z prefix))
                             then false
                             else (ad_simple_path_naive_search z y (cons x prefix) n0)) edges)).
      	Intro H2. Elim H2. Intro r. Elim r. Intros x0 d0 H6.
      	Cut (if (ad_in_list x0 (cons x prefix))
             then false
             else (ad_simple_path_naive_search x0 y (cons x prefix) n0))=true.
      	Intro. Elim (sumbool_of_bool (ad_in_list x0 (cons x prefix))). Intro H8.
      	Rewrite H8 in H7. Discriminate H7.
	Intro H8. Rewrite H8 in H7. Clear H2 H3. Elim (H x0 y (cons x prefix) (Dplus d0 d')).
      	Intros d1 H9. Elim H9. Intros l H10. Elim H10. Intros H11 H12.
      	Rewrite <- (ad_list_app_rev (cons x prefix) l x0) in H11.
      	Rewrite <- (ad_list_app_rev (cons x prefix) l x0) in H12. Split with d1.
      	Split with (cons x0 l). Split. Assumption.
	Assumption.
	Change (CG_path x0 (Dplus d0 d') (app (rev (cons x prefix)) (cons x0 (nil ad)))).
      	Apply CG_path_app_1 with x:=x. Rewrite <- (Dplus_z_d d0). Apply CG_p2. Apply CG_p1.
      	Reflexivity.
	Unfold CG_edge. Rewrite H5. Rewrite (MapSweep_semantics_2 ? ? edges x0 d0 H6).
      	Reflexivity.
	Assumption.
	Simpl. Simpl in H1. Rewrite H1. Simpl in H8. Rewrite H8. Reflexivity.
	Assumption.
	Exact (MapSweep_semantics_1 ? ? ? x0 d0 H6).
	Intro H2. Rewrite H2 in H3. Discriminate H3.
	Intro H4. Rewrite H4 in H3. Discriminate H3.
      Qed.

Lemma ad_simple_path_naive_search_complete : (n:nat) (x,y:ad)
      	   (ad_simple_path_naive_search x y (nil ad) n)=true ->
	     {d:D & {l:(list ad) & (and_sp (CG_path y d (cons x l))
	                                   (ad_list_stutters (cons x l))=false)}}.
      Proof.
      	Intros. Exact (ad_simple_path_naive_search_complete_1 n x y (nil ad) Dz
                       (CG_p1 x x (refl_equal ? ?)) (refl_equal ? false) H).
      Qed.

(*s Definition of simple paths : paths without repetition *)

Definition CG_simple_path := [last:ad] [d:D] [l:(list ad)]
                                   (and_sp (CG_path last d l) (ad_list_stutters l)=false).

(*s Between two vertexes, there exists a simple path or there exists no path *)
Lemma ad_simple_path_dec : (x,y:ad)
      	  {l:(list ad) & {d:D & (CG_simple_path y d (cons x l))}}+
	  {(l:(list ad)) (d:D) (CG_simple_path y d (cons x l)) -> False}.
      Proof.
      	Intros. Elim (sumbool_of_bool (ad_simple_path_naive_search x y (nil ad) (MapCard ? cg))).
      	Intro H. Left . Elim (ad_simple_path_naive_search_complete ? ? ? H). Intros d H0.
      	Elim H0. Intros l H1. Split with l. Split with d. Exact H1.
	Intro H. Right . Intros l d H0. Unfold CG_simple_path in H0. Elim H0. Intros H1 H2.
      	Rewrite (ad_simple_path_naive_search_correct ? x y l d
                  (le_S_n ? ? (ad_simple_path_bounded_card ? ? ? ? H1 H2)) H1 H2) in H.
      	Discriminate H.
      Qed.

(*s Computing the minimum of edges in a Map *)

Definition all_min := [f:ad->D->(option D)] (MapFold ? ? (NONE D) Ddmin f).

Lemma all_min_le_1 : (f:ad->D->(option D)) (m:(Map D))
      	  (a:ad) (d:D) (MapGet ? m a)=(SOME ? d) ->
            (Ddle (all_min f m) (f a d))=true.
      Proof.
      	Intros. Elim (option_sum ? (f a d)). Intro H0. Elim H0. Intros d' H1. Rewrite H1.
      	Unfold all_min. Cut ([a:(option D)][b:D](Ddle a (SOME D b))
                              (MapFold D (option D) (NONE D) Ddmin f m) d')
                            =(MapFold D bool false orb
                              [a:ad] [y:D]([a0:(option D)][b:D](Ddle a0 (SOME D b)) (f a y) d') m).
      	Intro. Rewrite H2. Rewrite MapFold_orb.
      	Elim (MapSweep_semantics_4 D [a:ad][y:D](Ddle (f a y) (SOME D d')) m a d H).
      	Intros a' H3. Elim H3. Intros d'' H4. Rewrite H4. Reflexivity.
	Rewrite H1. Simpl. Apply Dle_refl.
	Exact (MapFold_distr_r D ? (NONE D) Ddmin bool false orb D
               [a:(option D)][b:D](Ddle a (SOME D b))
               [c:D](refl_equal ? false)
               [a,b:(option D)][c:D](Ddmin_le_distr_l a b (SOME ? c)) f m d').
	Intro H0. Rewrite H0. (Case (all_min f m); Reflexivity).
      Qed.

Lemma all_min_le_2_1 : (f:ad->D->(option D)) (m:(Map D)) (pf:ad->ad)
      	  (d:D) (MapFold1 ? ? (NONE D) Ddmin f pf m)=(SOME ? d) ->
            {a:ad & {d':D | (MapGet ? m a)=(SOME ? d') /\ (f (pf a) d')=(SOME ? d)}}.
      Proof.
        Induction m. Intros. Discriminate H.
	Intros a y pf d H. Simpl in H. Split with a. Split with y. Split. Apply M1_semantics_1.
	Assumption.
	Intros. Simpl in H1.
      	Elim (Ddmin_choice
           (MapFold1 D (option D) (NONE D) Ddmin f [a0:ad](pf (ad_double a0)) m0)
           (MapFold1 D (option D) (NONE D) Ddmin f [a0:ad](pf (ad_double_plus_un a0)) m1)).
      	Intro H2. Rewrite H2 in H1. Elim (H [a0:ad](pf (ad_double a0)) d H1). Intros a0 H3.
      	Elim H3. Intros d' H4. Split with (ad_double a0). Split with d'. Split.
      	Rewrite MapGet_M2_bit_0_0. Rewrite ad_double_div_2. (Elim H4; Trivial).
	Apply ad_double_bit_0.
	(Elim H4; Trivial).
	Intro H2. Rewrite H2 in H1. Elim (H0 [a0:ad](pf (ad_double_plus_un a0)) d H1).
      	Intros a0 H3. Elim H3. Intros d' H4. Split with (ad_double_plus_un a0). Split with d'.
      	Split. Rewrite MapGet_M2_bit_0_1. Rewrite ad_double_plus_un_div_2. (Elim H4; Trivial).
	Apply ad_double_plus_un_bit_0.
	(Elim H4; Trivial).
      Qed.

Lemma all_min_le_2 : (f:ad->D->(option D)) (m:(Map D))
      	  (d:D) (all_min f m)=(SOME ? d) ->
            {a:ad & {d':D | (MapGet ? m a)=(SOME ? d') /\ (f a d')=(SOME ? d)}}.
      Proof.
      	Intros. Exact (all_min_le_2_1 f m [a:ad]a d H).
      Qed.

Lemma all_min_le_3 : (f,g:ad->D->(option D)) (m:(Map D))
      	  ((a:ad) (d:D) (MapGet ? m a)=(SOME ? d) -> (Ddle (f a d) (g a d))=true) ->
	  (Ddle (all_min f m) (all_min g m))=true.
      Proof.
      	Intros. Elim (option_sum ? (all_min g m)). Intro H0. Elim H0. Intros d H1.
      	Elim (all_min_le_2 g m d H1). Intros a H2. Elim H2. Intros d' H3. Elim H3. Intros H4 H5.
      	Apply Ddle_trans with (f a d'). Apply all_min_le_1. Assumption.
	Rewrite H1. Rewrite <- H5. Apply H. Assumption.
	Intro H0. Rewrite H0. Apply Ddle_d_none.
      Qed.

(*s [(ad_simple_path_dist_1 x y l n)] computes the minimum weight of a path 
    from [x] to [y] of maximal length [n] which does not contain vertexes 
    from [l] *)

Fixpoint ad_simple_path_dist_1 [x,y:ad; l:(list ad); n:nat] : (option D) :=
        if (ad_eq x y)
	then (SOME ? Dz)
	else
      	Cases n of
	    O => (NONE ?)
	  | (S n') => Cases (MapGet ? cg x) of
	                  NONE => (NONE ?)
			| (SOME edges) =>
                          let l'=(cons x l) in (* builds reverse path *)
			  (all_min [z:ad][d:D]
			           if (ad_in_list z l')
                                   then (NONE D)
				   else (Ddplus (ad_simple_path_dist_1 z y l' n') d)
				   edges)
                      end
        end.

Lemma ad_simple_path_dist_1_correct_1 : (n:nat) (x,y:ad) (l:(list ad)) (d:D)
      	  (le (length l) n) -> (CG_path y d (cons x l)) ->
      	  (prefix:(list ad))
      	    (ad_list_stutters (app (rev prefix) (cons x l)))=false ->
	    (Ddle (ad_simple_path_dist_1 x y prefix n) (SOME ? d))=true.
      Proof.
      	Induction n. Intros x y l. Case l. Intros. Inversion H0. 
        Rewrite H4. Simpl.
      	Rewrite (ad_eq_correct y). Rewrite H3. Apply Ddle_refl.
	Intros. Elim (le_Sn_O ? H).
	Intros n0 H x y l. Case l. Intros. Inversion H1. 
        Rewrite H5. Simpl.
      	Rewrite (ad_eq_correct y). Rewrite H4. Apply Ddle_refl.
	Intros. Simpl. Elim (sumbool_of_bool (ad_eq x y)). Intro H3. Rewrite H3.
      	Rewrite (ad_eq_complete ? ? H3) in H1. Exact (no_bad_cycles ? ? ? H1).
	Intro H3. Rewrite H3. Elim (option_sum ? (MapGet ? cg x)). Intro H4. Elim H4.
      	Intros edges H5. Rewrite H5. Inversion_clear H1.
      	Apply Ddle_trans with dd':=Case (ad_in_list a (cons x prefix)) of
              (NONE D)
              (Ddplus (ad_simple_path_dist_1 a y (cons x prefix) n0) d')
              end.
      	Cut (MapGet ? edges a)=(SOME ? d'). Intro.
      	Exact (all_min_le_1 [z:ad] [d:D]
          Case (orb (ad_eq z x) (ad_in_list z prefix)) of
             (NONE D)
             (Ddplus (ad_simple_path_dist_1 z y (cons x prefix) n0) d)
             end edges a d' H1).
	Unfold CG_edge in H7. Rewrite H5 in H7. Elim (option_sum ? (MapGet D edges a)). Intro H8.
      	Elim H8. Intros d1 H9. Rewrite H9 in H7. Rewrite H9. Inversion_clear H7. Reflexivity.
	Intro H8. Rewrite H8 in H7. Discriminate H7.
	Rewrite (ad_list_app_rev prefix (cons a l0) x) in H2.
      	Rewrite <- (ad_in_list_rev (cons x prefix) a).
      	Rewrite (ad_list_stutters_prev_conv_l ? ? ? H2).
      	Apply (Ddle_plus_mono (ad_simple_path_dist_1 a y (cons x prefix) n0) (SOME D d0) d' d').
      	Exact (H a y l0 d0 (le_S_n ? ? H0) H6 (cons x prefix) H2).
	Apply Dle_refl.
	Intro H4. Inversion H1. Unfold CG_edge in H10. 
        Rewrite H4 in H10. Discriminate H10.
      Qed.

Lemma ad_simple_path_dist_1_correct_2 : (n:nat) (x,y:ad) (l:(list ad)) (d:D)
      	  (le (length l) n) -> (CG_path y d (cons x l)) ->
      	    (ad_list_stutters (cons x l))=false ->
	    (Ddle (ad_simple_path_dist_1 x y (nil ad) n) (SOME ? d))=true.
      Proof.
      	Intros. Exact (ad_simple_path_dist_1_correct_1 n x y l d H H0 (nil ad) H1).
      Qed.

(*s [(ad_simple_path_dist x y)] computes the minimum path from x to y *)
Definition ad_simple_path_dist := [x,y:ad]
          (ad_simple_path_dist_1 x y (nil ad) (MapCard ? cg)).

Lemma ad_simple_path_dist_correct_1 : (x,y:ad) (l:(list ad)) (d:D)
      	  (CG_path y d (cons x l)) ->
      	  (ad_list_stutters (cons x l))=false ->
	    (Ddle (ad_simple_path_dist x y) (SOME ? d))=true.
      Proof.
      	Intros. Unfold ad_simple_path_dist.
      	(Apply ad_simple_path_dist_1_correct_2 with l:=l; Try Assumption).
      	Exact (le_S_n ? ? (ad_simple_path_bounded_card l y x d H H0)).
      Qed.

Lemma ad_simple_path_dist_correct : (x,y:ad) (l:(list ad)) (d:D)
      	  (CG_path y d (cons x l)) ->
	    (Ddle (ad_simple_path_dist x y) (SOME ? d))=true.
      Proof.
      	Intros. Elim ad_path_then_simple_path with 1:= H. 
        Intros l0 H0.
      	Elim H0. Intros d0 H1. Elim H1. Intros H2 H3. Elim H3. Intros H4 H5.
      	Apply Ddle_trans with dd':=(SOME D d0).
      	Exact (ad_simple_path_dist_correct_1 x y l0 d0 H2 H4).
	Exact H5.
      Qed.

Lemma ad_simple_path_dist_1_complete_1 : (n:nat) (x,y:ad) (prefix:(list ad))
      	   (d':D) (CG_path x d' (rev (cons x prefix))) ->
      	   (ad_list_stutters (cons x prefix))=false ->
	   (d0:D)
      	   (ad_simple_path_dist_1 x y prefix n)=(SOME D d0) ->
	     {l:(list ad) & (and_sp (CG_path y (Dplus d0 d') (app (rev (cons x prefix)) l))
	                            (ad_list_stutters (app (rev (cons x prefix)) l))=false /\
                                     (le (length l) n) )}.
      Proof.
      	Induction n. Intros. Split with (nil ad). Split. Unfold ad_simple_path_dist_1 in H1.
      	Elim (sumbool_of_bool (ad_eq x y)). Intro H2. Rewrite H2 in H1. Inversion H1.
      	Rewrite <- H4. Rewrite Dplus_z_d. Rewrite <- app_nil_end.
      	Rewrite <- (ad_eq_complete ? ? H2). Assumption.
	Intro H2. Rewrite H2 in H1. Discriminate H1.
	Split. Rewrite <- app_nil_end. Rewrite ad_list_stutters_rev. Assumption.
	Apply le_n.
	Intros. Simpl in H2. Elim (sumbool_of_bool (ad_eq x y)). Intro H3. Rewrite H3 in H2.
      	Inversion H2. Split with (nil ad). Split. Rewrite <- H5. Rewrite Dplus_z_d.
      	Rewrite <- app_nil_end. Rewrite <- (ad_eq_complete ? ? H3). Assumption.
	Split. Rewrite <- app_nil_end. Rewrite ad_list_stutters_rev. Assumption.
	Apply le_O_n.
	Intro H3. Rewrite H3 in H2. Elim (option_sum ? (MapGet ? cg x)). Intro H4. Elim H4.
      	Intros edges H5. Rewrite H5 in H2. Elim (all_min_le_2 ? edges d0 H2). Intros a H6.
      	Elim H6. Intros d1 H7. Elim H7. Intros H8 H9. Clear H2 H6 H7.
      	Cut (ad_in_list a (cons x prefix))=false. Intro.
      	Elim (option_sum ? (ad_simple_path_dist_1 a y (cons x prefix) n0)). Intro H6. Elim H6.
      	Intros d2 H7. Clear H6. Rewrite H7 in H9. Cut (Dplus d2 d1)=d0. Intro.
      	Cut (CG_path a (Dplus d1 d') (rev (cons a (cons x prefix)))). Intro.
      	Cut (ad_list_stutters (cons a (cons x prefix)))=false. Intro.
      	Elim (H a y (cons x prefix) ? H10 H11 d2 H7). Intros l0 H12. Elim H12. Intros H13 H14.
      	Elim H14. Intros H15 H16. Split with (cons a l0). Split. Rewrite ad_list_app_rev.
      	Rewrite <- H6. Rewrite Dplus_assoc. Assumption.
	Split. Rewrite ad_list_app_rev. Assumption.
	Exact (le_n_S ? ? H16).
	Simpl. Simpl in H2. Rewrite H2. Simpl in H1. Rewrite H1. Reflexivity.
	Apply (CG_path_app_1 (rev (cons x prefix)) (cons a (nil ad)) a x).
      	Rewrite <- (Dplus_z_d d1). Apply CG_p2. Apply CG_p1. Reflexivity.
	Unfold CG_edge. Rewrite H5. Rewrite H8. Reflexivity.
	Assumption.
	Elim (sumbool_of_bool (orb (ad_eq a x) (ad_in_list a prefix))). Intro H10.
      	Rewrite H10 in H9. Discriminate H9.
	Intro H10. Rewrite H10 in H9. Simpl in H9. Inversion H9. Reflexivity.
	Intro H6. Rewrite H6 in H9. Generalize H9.
      	Case (orb (ad_eq a x) (ad_in_list a prefix)); Intro H10; Discriminate H10.
	Elim (sumbool_of_bool (ad_in_list a (cons x prefix))). Intro H10. Simpl in H10.
      	Rewrite H10 in H9. Discriminate H9.
	Trivial.
	Intro H4. Rewrite H4 in H2. Discriminate H2.
      Qed.

Lemma ad_simple_path_dist_1_complete : (n:nat) (x,y:ad) (d:D)
      	   (ad_simple_path_dist_1 x y (nil ad) n)=(SOME D d) ->
	     {l:(list ad) & (and_sp (CG_path y d (cons x  l))
	                            (ad_list_stutters (cons x l))=false)}.
      Proof.
      	Intros. Elim (ad_simple_path_dist_1_complete_1 n x y (nil ad) Dz
                        (CG_p1 x x (refl_equal ? ?)) (refl_equal ? ?) d H).
      	Intros l H0. Split with l. Elim H0. Intros H1 H2. Elim H2. Intros H3 H4. Split.
      	Rewrite (Dplus_d_z d) in H1. Assumption.
	Exact H3.
      Qed.

Lemma ad_simple_path_dist_complete : (x,y:ad) (d:D)
      	   (ad_simple_path_dist x y)=(SOME D d) ->
	     {l:(list ad) & (and_sp (CG_path y d (cons x  l))
	                            (ad_list_stutters (cons x l))=false)}.
      Proof.
      	Intros. Exact (ad_simple_path_dist_1_complete (MapCard ? cg) x y d H).
      Qed.

Lemma ad_simple_path_dist_complete_2 : (x,y:ad) (d:D)
      	   (ad_simple_path_dist x y)=(SOME D d) ->
	     {l:(list ad) & (CG_path y d (cons x  l))}.
      Proof.
      	Intros. Elim (ad_simple_path_dist_complete x y d H). Intros l H0. Split with l.
      	(Elim H0; Trivial).
      Qed.

Lemma ad_simple_path_dist_complete_3 : (x,y:ad) (dd:(option D))
      	  ((l:(list ad)) (d:D) (CG_path y d (cons x l)) -> (Ddle dd (SOME ? d))=true) ->
	     (Ddle dd (ad_simple_path_dist x y))=true.
      Proof.
      	Intros x y dd. Case dd. Intros. Elim (option_sum ? (ad_simple_path_dist x y)). Intro H0.
      	Elim H0. Intros d H1. Elim (ad_simple_path_dist_complete_2 x y d H1). Intros l H2.
      	Simpl in H. Rewrite <- (H l d H2). Rewrite H1. Reflexivity.
	Intro H0. Rewrite H0. Reflexivity.
	Intros. Elim (option_sum ? (ad_simple_path_dist x y)). Intro H0. Elim H0. Intros d0 H1.
      	Rewrite H1. Elim (ad_simple_path_dist_complete_2 x y d0 H1). Intros l H2.
      	Exact (H l d0 H2).
	Intro H0. Rewrite H0. Reflexivity.
      Qed.

Lemma ad_simple_path_dist_d_1 : (x:ad) (ad_simple_path_dist x x)=(SOME ? Dz).
      Proof.
      	Unfold ad_simple_path_dist. (Elim (MapCard ? cg); Simpl). Intro.
      	Rewrite (ad_eq_correct x). Reflexivity.
	Intros. Rewrite (ad_eq_correct x). Reflexivity.
      Qed.

Lemma ad_simple_path_dist_d_2 : (x,y,z:ad) (d,d':D)
      	  (ad_simple_path_dist x y)=(SOME ? d) -> (ad_simple_path_dist y z)=(SOME ? d') ->
	    (Ddle (ad_simple_path_dist x z) (SOME ? (Dplus d' d)))=true.
      Proof.
      	Intros. Elim (ad_simple_path_dist_complete_2 x y d H).
      	Elim (ad_simple_path_dist_complete_2 y z d' H0). Intros l1 H1 l2 H2.
      	Apply (ad_simple_path_dist_correct x z (app l2 l1)).
      	Exact (CG_path_app_1 (cons x l2) l1 z y d d' H1 H2).
      Qed.

Lemma ad_simple_path_dist_d_3 : (x,y,z:ad) (d,d':D)
      	  (Ddle (ad_simple_path_dist x y) (SOME ? d))=true ->
          (Ddle (ad_simple_path_dist y z) (SOME ? d'))=true ->
	    (Ddle (ad_simple_path_dist x z) (SOME ? (Dplus d' d)))=true.
      Proof.
      	Intros. Elim (option_sum ? (ad_simple_path_dist x y)). Intro H1. Elim H1. Intros d0 H2.
      	Elim (option_sum ? (ad_simple_path_dist y z)). Intro H3. Elim H3. Intros d'0 H4.
      	Apply Ddle_trans with dd':=(SOME D (Dplus d'0 d0)).
      	Exact (ad_simple_path_dist_d_2 x y z d0 d'0 H2 H4).
	Rewrite H2 in H. Simpl in H. Rewrite H4 in H0. Simpl in H0. Simpl.
      	Exact (Dle_plus_mono ? ? ? ? H0 H).
	Intro H3. Rewrite H3 in H0. Discriminate H0.
	Intro H1. Rewrite H1 in H. Discriminate H.
      Qed.

(*s [(CG_leq x y)] is true when there is a path from [x] to [y] *)

Definition CG_leq := [x,y:ad] Cases (ad_simple_path_dist x y) of
                                         (SOME _) => true
				       | _ => false
				     end.

Lemma CG_leq_refl : (x:ad) (CG_leq x x)=true.
      Proof.
      	Unfold CG_leq. Intros. Rewrite (ad_simple_path_dist_d_1 x). Reflexivity.
      Qed.

Lemma CG_leq_trans : (x,y,z:ad) (CG_leq x y)=true -> (CG_leq y z)=true -> (CG_leq x z)=true.
      Proof.
      	Unfold CG_leq. Intros. Elim (option_sum ? (ad_simple_path_dist x y)). Intro H1.
      	Elim H1. Intros d1 H2. Elim (option_sum ? (ad_simple_path_dist y z)). Intro H3.
      	Elim H3. Intros d2 H4. Cut (Ddle (ad_simple_path_dist x z) (SOME D (Dplus d2 d1)))=true.
      	Intro. Elim (option_sum ? (ad_simple_path_dist x z)). Intro H6. Elim H6. Intros d3 H7.
      	Rewrite H7. Reflexivity.
	Intro H6. Rewrite H6 in H5. Discriminate H5.
	Exact (ad_simple_path_dist_d_2 ? ? ? ? ? H2 H4).
	Intro H3. Rewrite H3 in H0. Discriminate H0.
	Intro H1. Rewrite H1 in H. Discriminate H.
      Qed.

(*s [(CG_standard_rho root d0 others x)] computes [d0-d] when
     [root] and [x] are connected by a path of minimal 
     length [d] and [(others x)] when there are not connected 
*)

Definition CG_standard_rho 
  := [root:ad] [d0:D] [others:ad->D] [x:ad]
                 Cases (ad_simple_path_dist root x) of
                     (SOME d) => (Dplus d0 (Dneg d))
		   | NONE => (others x) (* dummy *)
		 end.

Lemma CG_standard_rho_root : (root:ad) (d0:D) (others:ad->D)
          (CG_standard_rho root d0 others root)=d0.
      Proof.
      	Unfold CG_standard_rho. Intros. Rewrite (ad_simple_path_dist_d_1 root).
      	Rewrite Dneg_Dz. Apply Dplus_d_z.
      Qed.

(*s If there is a root such that all the nodes ae connected to 
    this root, then [CG_standard_rho] gives a correct valuation 
*)
Lemma CG_rooted_sat_1 : (root:ad) (d0:D) (others:ad->D)
      	  ((x:ad) (in_dom ? x cg)=true -> (CG_leq root x)=true) ->
	    (CGsat (CG_standard_rho root d0 others)).
      Proof.
      	Unfold CG_standard_rho. Intros. Unfold CGsat. Intros.
      	Elim (option_sum ? (ad_simple_path_dist root x)). Intro H1. Elim H1. Intros d1 H2.
      	Rewrite H2. Cut (Ddle (ad_simple_path_dist root y) (SOME D (Dplus d d1)))=true. Intro.
      	Elim (option_sum ? (ad_simple_path_dist root y)). Intro H4. Elim H4. Intros d2 H5.
      	Rewrite H5. Rewrite Dplus_assoc. Apply Dle_plus_mono. Apply Dle_refl.
	Apply Dplus_reg_l with d'':=d2. Rewrite <- Dplus_assoc. Rewrite Dplus_neg.
      	Rewrite Dplus_z_d. Apply Dplus_reg_r with d'':=d1. Rewrite Dplus_assoc.
      	Rewrite Dplus_neg_2. Rewrite Dplus_d_z. Rewrite H5 in H3. Exact H3.
	Intro H4. Rewrite H4 in H3. Discriminate H3.
	Elim (ad_simple_path_dist_complete_2 root x d1 H2). Intros l H3.
      	Apply (ad_simple_path_dist_correct root y (app l (cons y (nil ad))) (Dplus d d1)).
      	Change (CG_path y (Dplus d d1) (app (cons root l) (cons y (nil ad)))).
      	Apply CG_path_app_1 with last:=y x:=x. Rewrite <- (Dplus_z_d d). Apply CG_p2.
      	Apply CG_p1. Reflexivity.
	Assumption.
	Assumption.
	Intro H1. Cut (CG_leq root x)=true. 
	Unfold CG_leq. Rewrite H1. Intro. Discriminate H2.
	Apply H. Rewrite MapDom_Dom. Exact (CG_edge_in_cg_1 ? ? ? H0).
      Qed.

Lemma CG_rooted_sat : (root:ad) (d0:D)
      	  ((x:ad) (in_dom ? x cg)=true -> (CG_leq root x)=true) ->
	    {rho:ad->D | (CGsat rho) /\ (rho root)=d0}.
      Proof.
      	Intros. Split with (CG_standard_rho root d0 [x:ad]d0). Split.
      	Exact (CG_rooted_sat_1 root d0 [x:ad]d0 H).
	Apply CG_standard_rho_root.
      Qed.

(*s The [CG_standard_rho] valuation is the minimal one *)
Lemma CG_standard_rho_minimal : (root:ad) (d0:D) (others:ad->D)
	    (rho:ad->D) (CGsat rho) -> (Dle d0 (rho root))=true ->
	      (x:ad) (CG_leq root x)=true ->
                (Dle (CG_standard_rho root d0 others x) (rho x))=true.
      Proof.
      	Unfold CG_leq CG_standard_rho. Intros. Elim (option_sum ? (ad_simple_path_dist root x)).
      	Intro H2. Elim H2. Intros d H3. Rewrite H3.
      	Elim (ad_simple_path_dist_complete_2 root x d H3). Intros l H4.
      	Apply Dplus_reg_r with d'':=d. Rewrite Dplus_assoc. Rewrite Dplus_neg_2.
      	Rewrite Dplus_d_z. Apply Dle_trans with d':=(rho root). Exact H0.
	Exact (CG_path_correct l root x d H4 rho H).
	Intro H2. Rewrite H2 in H1. Discriminate H1.
      Qed.

Lemma CG_sat_add_1 : (x,y:ad) (d:D)
          (rho:ad->D) (CGsat rho) -> (Dle (rho x) (Dplus (rho y) d))=true ->
            (Ddle (SOME ? (Dneg d)) (ad_simple_path_dist y x))=true.
      Proof.
      	Intros. Apply ad_simple_path_dist_complete_3. Intros. Simpl.
      	Apply Dplus_reg_r with d'':=d. Rewrite Dplus_neg_2. Apply Dplus_reg_l with d'':=(rho x).
      	Rewrite Dplus_d_z. Apply Dle_trans with d':=(Dplus (rho y) d); Try Assumption.
      	Apply Dle_trans with d':=(Dplus (Dplus (rho x) d0) d). Apply Dle_plus_mono.
      	Exact (CG_path_correct l y x d0 H1 rho H).
	Apply Dle_refl.
	Rewrite Dplus_assoc. Apply Dle_refl.
      Qed.

    End CGNoBadCycles.

(*s [(CG_add x y d)] adds the edge (x,y) of weight d to G, 
   in case an edge already exists, only the minimal one is kept
*)

Definition CG_add := [x,y:ad; d:D]
      Cases (MapGet ? cg x) of
          NONE => (MapPut ? cg x (M1 ? y d))
        | (SOME edges) => Cases (MapGet ? edges y) of
                              NONE => (MapPut ? cg x (MapPut ? edges y d))
  			    | (SOME d0) => (MapPut ? cg x (MapPut ? edges y (Dmin d d0)))
  	                end
      end.

End CGDist.

(*s Properties of [CG_add] *)
Section CGAdd.

    Variable cg1 : CGraph1.

    Variable x,y : ad.
    Variable d:D.

Definition cg2 := (CG_add cg1 x y d).

Lemma CG_add_edge_1 : (x0,y0:ad) (CG_edge cg2 x0 y0)=
              (if (andb (ad_eq x x0) (ad_eq y y0))
		 then (Ddmin (SOME ? d) (CG_edge cg1 x0 y0))
		 else (CG_edge cg1 x0 y0)).
    Proof.
    	Unfold cg2 CG_add. Intros. Elim (sumbool_of_bool (andb (ad_eq x x0) (ad_eq y y0))).
    	Intro H. Elim (andb_prop ? ? H). Intros H0 H1. Rewrite H.
    	Rewrite <- (ad_eq_complete ? ? H0). Rewrite <- (ad_eq_complete ? ? H1).
    	Elim (option_sum ? (MapGet ? cg1 x)). Intro H2. Elim H2. Intros edges H3. Rewrite H3.
    	Elim (option_sum ? (MapGet D edges y)). Intro H4. Elim H4. Intros d0 H5. Rewrite H5.
    	Unfold CG_edge. Rewrite (MapPut_semantics ? cg1 x (MapPut D edges y (Dmin d d0)) x).
    	Rewrite (ad_eq_correct x). Rewrite (MapPut_semantics ? edges y (Dmin d d0) y).
    	Rewrite (ad_eq_correct y). Rewrite H3. Rewrite H5. Reflexivity.
	Intro H4. Rewrite H4. Unfold CG_edge.
    	Rewrite (MapPut_semantics ? cg1 x (MapPut D edges y d) x). Rewrite (ad_eq_correct x).
    	Rewrite H3. Rewrite H4. Rewrite (MapPut_semantics ? edges y d y).
    	Rewrite (ad_eq_correct y). Reflexivity.
	Intro H2. Rewrite H2. Unfold CG_edge. Rewrite (MapPut_semantics ? cg1 x (M1 D y d) x).
    	Rewrite (ad_eq_correct x). Rewrite H2. Rewrite (M1_semantics_1 ? y d). Reflexivity.
	Intro H. Rewrite H. Elim (andb_false_elim ? ? H). Intro H0.
    	Elim (option_sum ? (MapGet ? cg1 x)). Intro H1. Elim H1. Intros edges H2. Rewrite H2.
    	Elim (option_sum ? (MapGet ? edges y)). Intro H3. Elim H3. Intros d0 H4. Rewrite H4.
    	Unfold CG_edge. Rewrite (MapPut_semantics ? cg1 x (MapPut D edges y (Dmin d d0)) x0).
    	Rewrite H0. Reflexivity.
	Intro H3. Rewrite H3. Unfold CG_edge.
    	Rewrite (MapPut_semantics ? cg1 x (MapPut D edges y d) x0). Rewrite H0. Reflexivity.
	Intro H1. Rewrite H1. Unfold CG_edge. Rewrite (MapPut_semantics ? cg1 x (M1 D y d) x0).
    	Rewrite H0. Reflexivity.
	Intro H0. Elim (option_sum ? (MapGet ? cg1 x)). Intro H1. Elim H1. Intros edges H2.
    	Rewrite H2. Elim (option_sum ? (MapGet ? edges y)). Intro H3. Elim H3. Intros d0 H4.
    	Rewrite H4. Unfold CG_edge.
    	Rewrite (MapPut_semantics ? cg1 x (MapPut D edges y (Dmin d d0)) x0).
    	Elim (sumbool_of_bool (ad_eq x x0)). Intro H5. Rewrite H5.
    	Rewrite (MapPut_semantics ? edges y (Dmin d d0) y0). Rewrite H0.
    	Rewrite <- (ad_eq_complete ? ? H5). Rewrite H2. Reflexivity.
	Intro H5. Rewrite H5. Reflexivity.
	Intro H3. Rewrite H3. Unfold CG_edge.
    	Rewrite (MapPut_semantics ? cg1 x (MapPut D edges y d) x0).
    	Elim (sumbool_of_bool (ad_eq x x0)). Intro H4. Rewrite H4.
    	Rewrite <- (ad_eq_complete ? ? H4). Rewrite H2.
    	Rewrite (MapPut_semantics ? edges y d y0). Rewrite H0. Reflexivity.
	Intro H4. Rewrite H4. Reflexivity.
	Intro H1. Rewrite H1. Unfold CG_edge. Rewrite (MapPut_semantics ? cg1 x (M1 D y d) x0).
    	Elim (sumbool_of_bool (ad_eq x x0)). Intro H2. Rewrite H2.
    	Rewrite (M1_semantics_2 ? y y0 d H0). Rewrite <- (ad_eq_complete ? ? H2).
    	Rewrite H1. Reflexivity.
	Intro H2. Rewrite H2. Reflexivity.
    Qed.

Lemma CG_add_edge_2 : (x0,y0:ad) (Ddle (CG_edge cg2 x0 y0) (CG_edge cg1 x0 y0))=true.
    Proof.
    	Intros. Rewrite (CG_add_edge_1 x0 y0).
    	Elim (sumbool_of_bool (andb (ad_eq x x0) (ad_eq y y0))). Intro H. Rewrite H.
    	Apply Ddmin_le_2.
	Intro H. Rewrite H. Apply Ddle_refl.
    Qed.

Lemma CG_add_1 : (rho:ad->D)
        (CGsat cg1 rho) -> (Dle (rho x) (Dplus (rho y) d))=true
          -> (CGsat cg2 rho).
    Proof.
    	Unfold CGsat. Intros. Rewrite (CG_add_edge_1 x0 y0) in H1.
    	Elim (sumbool_of_bool (andb (ad_eq x x0) (ad_eq y y0))). Intro H2.
    	Elim (andb_prop ? ? H2). Intros H3 H4. Rewrite H2 in H1.
    	Rewrite <- (ad_eq_complete ? ? H3). Rewrite <- (ad_eq_complete ? ? H4).
    	Elim (option_sum ? (CG_edge cg1 x0 y0)). Intro H5. Elim H5. Intros d1 H6.
    	Rewrite H6 in H1. Simpl in H1. Inversion H1. Rewrite Dmin_plus_r. Apply Dmin_le_5.
    	Assumption.
	Apply H. Rewrite (ad_eq_complete ? ? H3). Rewrite (ad_eq_complete ? ? H4). Assumption.
	Intro H5. Rewrite H5 in H1. Simpl in H1. Inversion H1. Rewrite <- H7. Assumption.
	Intro H2. Rewrite H2 in H1. Apply H. Assumption.
    Qed.

Lemma CG_add_2 : (rho:ad->D) (CGsat cg2 rho) -> (CGsat cg1 rho).
    Proof.
    	Unfold CGsat. Intros. Elim (option_sum ? (CG_edge cg2 x0 y0)). Intro H1. Elim H1.
    	Intros d1 H2. Cut (Dle d1 d0)=true. Intro H3.
    	Apply Dle_trans with d':=(Dplus (rho y0) d1). Apply H. Assumption.
	Apply Dle_plus_mono. Apply Dle_refl.
	Assumption.
	Change (Ddle (SOME ? d1) (SOME ? d0))=true. Rewrite <- H2. Rewrite <- H0.
    	Apply CG_add_edge_2.
	Intro H1. Cut (Ddle (NONE ?) (SOME ? d0))=true. Intro H2. Discriminate H2.
	Rewrite <- H1. Rewrite <- H0. Apply CG_add_edge_2.
    Qed.

Lemma CG_add_3 : (rho:ad->D) (CGsat cg2 rho) -> (Dle (rho x) (Dplus (rho y) d))=true.
    Proof.
    	Unfold CGsat. Intros. Elim (option_sum ? (CG_edge cg2 x y)). Intro H0. Elim H0.
    	Intros d0 H1. Apply Dle_trans with d':=(Dplus (rho y) d0). Apply H. Assumption.
	Apply Dle_plus_mono. Apply Dle_refl.
	Rewrite (CG_add_edge_1 x y) in H1. Rewrite (ad_eq_correct x) in H1.
    	Rewrite (ad_eq_correct y) in H1. Simpl in H1. Elim (option_sum ? (CG_edge cg1 x y)).
    	Intro H2. Elim H2. Intros d1 H3. Rewrite H3 in H1. Inversion H1. Apply Dmin_le_1.
	Intro H2. Rewrite H2 in H1. Inversion H1. Apply Dle_refl.
	Intro H0. Rewrite (CG_add_edge_1 x y) in H0. Rewrite (ad_eq_correct x) in H0.
    	Rewrite (ad_eq_correct y) in H0. Simpl in H0. Generalize H0.
    	(Case (CG_edge cg1 x y); Intro H1). Discriminate H1.
	Intro H2. Discriminate H2.
    Qed.

(*s Every path in the new graph [cg2] either goes through the new edge from [x] to [y],
       or is a path in the old graph cg1: 
*)
Lemma CG_add_4_1 : (l:(list ad)) (x0,y0:ad) (d0:D) (CG_path cg2 y0 d0 (cons x0 l)) ->
    	  {l0:(list ad) & {l1:(list ad) | (cons x0 l)=(app l0 (cons x (cons y l1)))}}+
	  (CG_path cg1 y0 d0 (cons x0 l)).
    Proof.
    	Induction l. Intros. Inversion H. Right . Rewrite H2.
        Rewrite <- H1. Apply CG_p1.
    	Reflexivity.
	Intros. Inversion H0. Rewrite (CG_add_edge_1 x0 a) in H6.
    	Elim (sumbool_of_bool (andb (ad_eq x x0) (ad_eq y a))). Intro H8. Left .
    	Split with (nil ad). Split with l0. Elim (andb_prop ? ? H8). Intros H9 H10.
    	Rewrite (ad_eq_complete ? ? H9). Rewrite (ad_eq_complete ? ? H10). Reflexivity.
	Intro H8. Elim (H ? ? ? H4). Intro H9. Elim H9. Intros l2 H10. Elim H10. Intros l3 H11.
    	Left . Split with (cons x0 l2). Split with l3. Rewrite H11. Reflexivity.
	Intro H9. Right . Apply CG_p2. Assumption.
	Rewrite H8 in H6. Assumption.
    Qed.

Lemma CG_add_4_2 : (l:(list ad)) (last:ad) (d0:D)
    	  (CG_path cg2 last d0 l) -> (ad_in_list y l)=false -> (CG_path cg1 last d0 l).
    Proof.
      Induction l. Intros. Inversion H.
	Intros a l0. Case l0. Intros. Inversion H0. Rewrite <- H3. Apply CG_p1. Assumption.
	Intros. Inversion H0. Rewrite (CG_add_edge_1 a a0) in H7. Elim (orb_false_elim ? ? H1).
    	Intros H9 H10. Elim (orb_false_elim ? ? H10). 
        Intros H11 H12. Rewrite H11 in H7.
    	Rewrite (andb_b_false (ad_eq x a)) in H7. Apply CG_p2. Apply H. Assumption.
	Exact H10.
	Assumption.
    Qed.

Lemma CG_add_4_3 : (x0:ad) (d0:D) (l:(list ad))
        (ad_list_stutters (cons y l))=false ->
	  (CG_path cg2 x0 d0 (cons y l)) -> (CG_path cg1 x0 d0 (cons y l)).
    Proof.
    	Intros x0 d0 l. Elim l. Intros. Inversion H0. 
        Rewrite <- H2. Apply CG_p1. Assumption.
	Intros. Inversion H1. Apply CG_p2. Apply CG_add_4_2. 
        Assumption.
	Elim (orb_false_elim ? ? H0). Trivial.
	Rewrite (CG_add_edge_1 y a) in H7. 
        Elim (orb_false_elim ? ? H0). Intros.
    	Elim (orb_false_elim ? ? H8). Intros. Rewrite H10 in H7.
    	Rewrite (andb_b_false (ad_eq x y)) in H7. Assumption.
    Qed.

Lemma CG_add_4_4 : (l:(list ad)) (last:ad) (d0:D)
    	  (CG_path cg2 last d0 l) -> (ad_in_list x l)=false -> (CG_path cg1 last d0 l).
    Proof.
    	Induction l. Intros. Inversion H.
	Intros a l0. Case l0. Intros. Inversion H0. Rewrite <- H3. Apply CG_p1. Assumption.
	Intros. Inversion H0. Apply CG_p2. Apply H. Assumption.
	Elim (orb_false_elim ? ? H1). Trivial.
	Rewrite (CG_add_edge_1 a a0) in H7. Elim (orb_false_elim ? ? H1). Intros.
    	Rewrite H8 in H7. Exact H7.
    Qed.

Lemma CG_add_4_5 : (d0:D) (l:(list ad))
        (ad_list_stutters (app l (cons x (nil ad))))=false ->
	  (CG_path cg2 x d0 (app l (cons x (nil ad)))) ->
          (CG_path cg1 x d0 (app l (cons x (nil ad)))).
    Proof.
    	Intros d0 l. Cut {l0:(list ad) & {y0:ad | l=(app l0 (cons y0 (nil ad)))}}+{l=(nil ad)}.
    	Intro. Elim H. Intro H0. Elim H0. Intros l0 H1. Elim H1. Intros y0 H2 H3 H4.
    	Rewrite H2 in H4. Rewrite (app_ass l0 (cons y0 (nil ad)) (cons x (nil ad))) in H4.
    	Simpl in H4. Elim (CG_path_app_3 cg2 l0 (cons x (nil ad)) x y0 d0 H4). Intros d1 H5.
    	Rewrite H2. Rewrite (app_ass l0 (cons y0 (nil ad)) (cons x (nil ad))). Simpl.
    	Elim (CG_path_app_2 cg2 l0 (cons x (nil ad)) x y0 d0 H4). Intros d2 H6.
    	Cut d0=(Dplus d2 d1). Intro. Rewrite H7.
    	Change (CG_path cg1 x (Dplus d2 d1) (app l0 (app (cons y0 (nil ad)) (cons x (nil ad))))).
    	Rewrite <- (app_ass l0 (cons y0 (nil ad)) (cons x (nil ad))).
    	Apply CG_path_app_1 with last:=x x:=y0. Inversion H6. 
        Inversion H11. Apply CG_p2.
    	Rewrite <- H15. Apply CG_p1. Assumption.
	Rewrite (CG_add_edge_1 y0 x) in H13. Rewrite H2 in H3.
    	Rewrite (app_ass l0 (cons y0 (nil ad)) (cons x (nil ad))) in H3. Simpl in H3.
    	Elim (orb_false_elim ? ? (ad_list_stutters_app_conv_r ? ? H3)). Intros.
    	Elim (orb_false_elim ? ? H17). Intros. 
        Rewrite (ad_eq_comm y0 x) in H19.
    	Rewrite H19 in H13. 
        Rewrite (andb_false_b (ad_eq y x)) in H13. Assumption.
	Apply CG_add_4_4. Assumption.
	Rewrite H2 in H3. Apply ad_list_stutters_prev_conv_l with l':=(nil ad). Assumption.
	Elim (CG_path_weight_and_last_unique cg2
             (app l0 (cons y0 (cons x (nil ad)))) x x d0 (Dplus d2 d1)).
    	Trivial.
	Assumption.
	Change (CG_path cg2 x (Dplus d2 d1) (app l0 (app (cons y0 (nil ad)) (cons x (nil ad))))).
    	Rewrite <- (app_ass l0 (cons y0 (nil ad)) (cons x (nil ad))).
    	Apply CG_path_app_1 with x:=y0. Assumption.
	Assumption.
	Intro H0. Rewrite H0. Simpl. Intros. Inversion H2. 
        Rewrite <- H4. Apply CG_p1.
    	Assumption.
	Elim l. Right . Reflexivity.
	Intros. Elim H. Intro H0. Elim H0. Intros l1 H1. Elim H1. Intros a0 H2. Rewrite H2.
    	Left . Split with (cons a l1). Split with a0. Reflexivity.
	Intro H0. Rewrite H0. Left . Split with (nil ad). Split with a. Reflexivity.
    Qed.

(*s If there is no cycle of negative weight in the old graph [cg1], and the distance
   from [y] to [x] is $\geq -d$, then there is no simple cycle of negative weight in 
   the new graph  [cg2] either: *)

Lemma CG_add_4 :
        ((x0:ad) (d0:D) (l:(list ad)) (CG_path cg1 x0 d0 (cons x0 l)) -> (Dle Dz d0)=true) ->
	  (Ddle (SOME ? (Dneg d)) (ad_simple_path_dist cg1 y x))=true ->
	    (x0:ad) (d0:D) (l:(list ad)) (CG_path cg2 x0 d0 (cons x0 l)) ->
                  (ad_list_stutters l)=false -> (Dle Dz d0)=true.
    Proof.
    	Intros. Elim (CG_add_4_1 ? ? ? ? H1). Intro H3. Elim H3. Intros l0 H4. Elim H4.
    	Intros l1 H5. Rewrite H5 in H1.
    	Change (CG_path cg2 x0 d0 (app l0 (app (cons x (nil ad)) (cons y l1)))) in H1.
    	Elim (CG_path_app_4 cg2 ? ? ? ? ? H1). Intros d1 H6. Elim H6. Intros d2 H7.
    	Elim H7. Intros H8 H9. Elim H8. Intros H10 H11. Clear H3 H6 H7 H8. Rewrite H9.
    	Inversion_clear H11. Rewrite (CG_add_edge_1 x y) in H6. Rewrite (ad_eq_correct x) in H6.
    	Rewrite (ad_eq_correct y) in H6. Simpl in H6. Apply Dplus_reg_r with d'':=(Dneg d1).
    	Rewrite Dplus_assoc. Rewrite Dplus_neg. Rewrite Dplus_d_z. Rewrite Dplus_z_d.
    	Apply Dplus_reg_l with d'':=d1. Rewrite Dplus_neg. Rewrite <- Dplus_assoc.
    	Change (cons x0 l)=(app l0 (app (cons x (nil ad)) (cons y l1))) in H5.
    	Rewrite (ass_app l0 (cons x (nil ad)) (cons y l1)) in H5.
    	Cut {l'0:(list ad) | (app l0 (cons x (nil ad)))=(cons x0 l'0)}. Intro H7. Elim H7.
    	Intros l'0 H8. Clear H4 H7. Rewrite H8 in H5. Simpl in H5. Inversion H5. Rewrite H8 in H10.
    	Cut (CG_path cg1 x (Dplus d1 d3) (cons y (app l1 l'0))). Intro.
    	Elim (option_sum ?  (CG_edge cg1 x y)). Intro H11. Elim H11. Intros d'0 H12.
    	Rewrite H12 in H6. Inversion_clear H6. Elim (Dmin_choice d d'0). Intro H13. Rewrite H13.
    	Apply Dplus_reg_r with d'':=(Dneg d). Rewrite Dplus_assoc. Rewrite Dplus_neg.
    	Rewrite Dplus_d_z. Rewrite Dplus_z_d.
    	Change (Ddle (SOME D (Dneg d)) (SOME D (Dplus d1 d3)))=true.
    	Apply Ddle_trans with dd':=(ad_simple_path_dist cg1 y x). Assumption.
	Exact (ad_simple_path_dist_correct cg1 H y x ? ? H4).
	Intro H13. Rewrite H13. Apply (H x (Dplus (Dplus d1 d3) d'0) (cons y (app l1 l'0))).
    	Apply (CG_path_app_1 cg1 (cons x (cons y (nil ad))) (app l1 l'0) x y). Assumption.
	Rewrite <- (Dplus_z_d d'0). Apply CG_p2. Apply CG_p1. Reflexivity.
	Assumption.
	Intro H11. Rewrite H11 in H6. Inversion H6. Rewrite <- H13.
    	Apply Dplus_reg_r with d'':=(Dneg d). Rewrite Dplus_assoc. Rewrite Dplus_neg.
    	Rewrite Dplus_d_z. Rewrite Dplus_z_d.
    	Change (Ddle (SOME D (Dneg d)) (SOME D (Dplus d1 d3)))=true.
    	Apply Ddle_trans with dd':=(ad_simple_path_dist cg1 y x). Assumption.
	Exact (ad_simple_path_dist_correct cg1 H y x ? ? H4).
	Apply (CG_path_app_1 cg1 (cons y l1) l'0 x x0). Rewrite <- H8. Apply CG_add_4_5.
    	Rewrite H8. Elim (CG_path_last cg2 ? ? ? H3). Intros l'1 H11. Rewrite H7 in H2.
    	Simpl. Rewrite (ad_list_stutters_app_conv_l ? ? H2). Rewrite H11 in H2.
    	Rewrite (ass_app l'0 l'1 (cons x0 (nil ad))) in H2.
    	Elim (sumbool_of_bool (ad_in_list x0 l'0)). Intro H12.
    	Rewrite (ad_list_stutters_prev_l ? (nil ad) ? (ad_in_list_l l'0 l'1 x0 H12)) in H2.
    	Discriminate H2.
	Intro H12. Rewrite H12. Reflexivity.
	Rewrite H8. Assumption.
	Apply CG_add_4_3. Rewrite H7 in H2. Exact (ad_list_stutters_app_conv_r l'0 (cons y l1) H2).
	Assumption.
	Generalize H5. Elim l0. Simpl. Intro H7. Exists (nil ad). Inversion_clear H7. Reflexivity.
	Intros. Rewrite (app_ass (cons a l2) (cons x (nil ad)) (cons y l1)) in H8. Simpl in H8.
    	Exists (app l2 (cons x (nil ad))). Inversion_clear H8. Reflexivity.
	Intro H3. Exact (H x0 d0 l H3).
    Qed.

Lemma CG_add_5_1 : (n:nat)
        ((x0:ad) (d0:D) (l:(list ad)) (CG_path cg1 x0 d0 (cons x0 l)) -> (Dle Dz d0)=true) ->
	  (Ddle (SOME ? (Dneg d)) (ad_simple_path_dist cg1 y x))=true ->
	    (x0:ad) (d0:D) (l:(list ad)) (CG_path cg2 x0 d0 (cons x0 l)) ->
            (le (length l) n) -> (Dle Dz d0)=true.
    Proof.
    	Induction n. Induction l. Intros. Inversion H1. Apply Dle_refl.
	Intros. Elim (le_Sn_O ? H3).
	Intros. Elim (sumbool_of_bool (ad_list_stutters l)). Intros H4.
    	Elim (ad_list_stutters_has_circuit l H4). Intros y0 H5. Elim H5. Intros l0 H6. Elim H6.
    	Intros l1 H7. Elim H7. Intros l2 H8. Rewrite H8 in H2.
    	Elim (CG_path_app_4 cg2 (cons x0 l0) (app l1 (cons y0 l2)) x0 y0 d0 H2). Intros d1 H9.
    	Elim H9. Intros d2 H10. Elim H10. Intros H11 H12. Elim H11. Intros H13 H14.
    	Clear H5 H6 H7 H9 H10 H11. Elim (CG_path_app_4 cg2 (cons y0 l1) l2 x0 y0 d2 H14).
    	Intros d3 H5. Elim H5. Intros d4 H6. Elim H6. Intros H7 H9. Elim H7. Intros H10 H11.
    	Clear H5 H6 H7 H14. Rewrite H12. Rewrite H9. Apply Dle_trans with d':=(Dplus d4 d1).
    	Apply (H H0 H1 x0 (Dplus d4 d1) (app l0 (cons y0 l2))).
    	Cut (cons x0 (app l0 (cons y0 l2)))=(app (app (cons x0 l0) (cons y0 (nil ad))) l2).
    	Intro. Rewrite H5. Exact (CG_path_app_1 cg2 ? ? ? ? ? ? H11 H13).
	Exact (ass_app (cons x0 l0) (cons y0 (nil ad)) l2).
	Rewrite ad_list_app_length. Apply le_S_n. Apply le_trans with m:=(length l).
    	Rewrite H8. Rewrite ad_list_app_length. Simpl. Rewrite ad_list_app_length. Simpl.
    	Rewrite <- plus_Snm_nSm. Rewrite <- plus_Snm_nSm. Rewrite <- plus_Snm_nSm. Simpl.
    	Rewrite <- plus_Snm_nSm. Simpl. Apply le_n_S. Apply le_n_S. Apply le_reg_l.
    	Apply le_plus_r. Assumption.
	Apply Dle_plus_mono. Apply Dle_trans with (Dplus d4 Dz). Rewrite Dplus_d_z. Apply Dle_refl.
    	Apply Dle_plus_mono. Apply Dle_refl.
    	Apply (H H0 H1 y0 d3 (app l1 (cons y0 (nil ad))) H10). Rewrite ad_list_app_length. Simpl.
    	Apply le_S_n. Apply le_trans with m:=(length l). Rewrite H8. Rewrite ad_list_app_length.
    	Simpl. Rewrite ad_list_app_length. Simpl. Rewrite <- plus_Snm_nSm. Rewrite <- plus_Snm_nSm.
    	Rewrite <- plus_Snm_nSm. Simpl. Rewrite <- plus_Snm_nSm. Simpl. Apply le_n_S. Apply le_n_S.
    	Apply le_trans with m:=(plus (length l1) (length l2)). Apply le_plus_plus. Apply le_n.
    	Apply le_O_n. Apply le_plus_r. Assumption.
	Apply Dle_refl.
	Intro H4. Exact (CG_add_4 H0 H1 x0 d0 l H2 H4).
    Qed.

Lemma CG_add_5 :
        ((x0:ad) (d0:D) (l:(list ad)) (CG_path cg1 x0 d0 (cons x0 l)) -> (Dle Dz d0)=true) ->
	  (Ddle (SOME ? (Dneg d)) (ad_simple_path_dist cg1 y x))=true ->
	    (x0:ad) (d0:D) (l:(list ad)) (CG_path cg2 x0 d0 (cons x0 l)) -> (Dle Dz d0)=true.
    Proof.
    	Intros. Exact (CG_add_5_1 (length l) H H0 x0 d0 l H1 (le_n ?)).
    Qed.

  End CGAdd.

(*s Properties of the range of the graph *)

Definition cg_range := (DMerge D).

Lemma cg_range_1 
  : (cg:CGraph1) (x,y:ad) (d:D) 
    (CG_edge cg x y)=(SOME ? d) -> (in_dom D y (cg_range cg))=true.
  Proof.
    Unfold cg_range CG_edge. Intros. Elim (option_sum ? (MapGet ? cg x)). Intro H0. Elim H0.
    Intros edges H1. Rewrite H1 in H. Apply in_dom_DMerge_3 with a:=x m0:=edges. Assumption.
    Unfold in_dom. Generalize H. Case (MapGet D edges y). Intro H2. Discriminate H2.
    Trivial.
    Intro H0. Rewrite H0 in H. Discriminate H.
  Qed.

Lemma cg_range_2 
  : (cg:CGraph1) (y:ad) (in_dom D y (cg_range cg))=true ->
      {x:ad & {d:D | (CG_edge cg x y)=(SOME ? d)}}.
  Proof.
    Intros. Elim (in_dom_DMerge_2 ? cg y H). Intros x H0. Elim H0. Intros edges H1. Elim H1.
    Intros H2 H3. Split with x. Elim (in_dom_some ? edges y H3). Intros d H4. Split with d.
    Unfold CG_edge. Rewrite H2. Rewrite H4. Reflexivity.
  Qed.

Lemma cg_range_4 : (cg:CGraph1) (x,y:ad) (d:D) (a:ad)
    	(in_dom D a (cg_range (CG_add cg x y d)))=(orb (ad_eq a y) (in_dom D a (cg_range cg))).
  Proof.
    Intros. Elim (sumbool_of_bool (in_dom D a (cg_range (CG_add cg x y d)))). Intro H.
    Elim (cg_range_2 ? ? H). Intros a0 H0. Elim H0. Intros d0 H1. Clear H0.
    Change (CG_edge (cg2 cg x y d) a0 a)=(SOME D d0) in H1.
    Rewrite (CG_add_edge_1 cg x y d a0 a) in H1. Rewrite H.
    Elim (sumbool_of_bool (andb (ad_eq x a0) (ad_eq y a))). Intro H2. Elim (andb_prop ? ? H2).
    Intros H3 H4. Rewrite (ad_eq_comm y a) in H4. Rewrite H4. Reflexivity.
    Intro H2. Rewrite H2 in H1. Rewrite (cg_range_1 ? ? ? ? H1). Apply sym_eq. Apply orb_b_true.
    Intro H. Rewrite H. Elim (sumbool_of_bool (ad_eq a y)). Intro H0.
    Rewrite (ad_eq_complete ? ? H0) in H. Cut {d0:D | (CG_edge (cg2 cg x y d) x y)=(SOME ? d0)}.
    Intro H1. Elim H1. Intros d0 H2. Unfold cg2 in H2. Rewrite (cg_range_1 ? ? ? ? H2) in H.
    Discriminate H.
    Rewrite (CG_add_edge_1 cg x y d x y). Rewrite (ad_eq_correct x). Rewrite (ad_eq_correct y).
    Case (CG_edge cg x y). Split with d. Reflexivity.
    Intro d0. Split with (Dmin d d0). Reflexivity.
    Intro H0. Rewrite H0. Elim (sumbool_of_bool (in_dom D a (cg_range cg))). Intro H1.
    Elim (cg_range_2 ? ? H1). Intros a0 H2. Elim H2. Intros d0 H3.
    Cut {d1:D | (CG_edge (cg2 cg x y d) a0 a)=(SOME ? d1)}. Intro H4. Elim H4. Intros d1 H5.
    Unfold cg2 in H5. Rewrite (cg_range_1 ? ? ? ? H5) in H. Discriminate H.
    Rewrite (CG_add_edge_1 cg x y d a0 a). Rewrite (ad_eq_comm a y) in H0. Rewrite H0.
    Rewrite (andb_b_false (ad_eq x a0)). Split with d0. Assumption.
    Intro H1. Rewrite H1. Reflexivity.
  Qed.

Lemma cg_out_of_range_1 : (cg:CGraph1) (y:ad) (in_dom D y (cg_range cg))=false ->
    	(x:ad) (CG_edge cg x y)=(NONE D).
  Proof.
    Intros. Elim (option_sum ? (CG_edge cg x y)). Intro H0. Elim H0. Intros d H1.
    Rewrite (cg_range_1 cg x y d H1) in H. Discriminate H.
    Trivial.
  Qed.

Lemma cg_out_of_range_2 : (cg:CGraph1) (y:ad) (in_dom D y (cg_range cg))=false ->
    	(x:ad) (ad_eq x y)=false -> (ad_simple_path_dist cg x y)=(NONE D).
  Proof.
    Intros. Elim (option_sum ? (ad_simple_path_dist cg x y)). Intro H1. Elim H1. Intros d H2.
    Elim (ad_simple_path_dist_complete_2 cg x y d H2). Intros l H3.
    Cut {a:ad & {d':D | (CG_edge cg a y)=(SOME ? d')}}. Intro H4. Elim H4. Intros a H5. Elim H5.
    Intros d' H6. Rewrite (cg_out_of_range_1 cg y H a) in H6. Discriminate H6.
    Generalize x H0 d H3. Elim l. Intros. Inversion H5. 
    Rewrite H8 in H4.
    Rewrite (ad_eq_correct y) in H4. Discriminate H4.
    Intros. Inversion H6. Elim (sumbool_of_bool (ad_eq a y)). 
    Intro H14. Split with x0.
    Split with d'. Rewrite <- (ad_eq_complete ? ? H14). Assumption.
    Intro H14. Exact (H4 a H14 ? H10).
    Trivial.
  Qed.

Lemma cg_out_of_range_3 : (cg:CGraph1) (y:ad) (in_dom D y (cg_range cg))=false ->
    	(x:ad) (ad_eq x y)=false -> (CG_leq cg x y)=false.
  Proof.
    Intros. Unfold CG_leq. Rewrite (cg_out_of_range_2 cg y H x H0). Reflexivity.
  Qed.

Lemma cg_add_out_of_range_1 : (cg:(CGraph1)) (x,y:ad) (d:D)
    	((x0:ad) (d0:D) (l:(list ad)) (CG_path cg x0 d0 (cons x0 l)) -> (Dle Dz d0)=true) ->
	(in_dom D x (cg_range cg))=false ->
	(ad_eq y x)=false ->
	  (x0:ad) (d0:D) (l:(list ad)) (CG_path (CG_add cg x y d) x0 d0 (cons x0 l)) ->
           (Dle Dz d0)=true.
  Proof.
    Intros. Apply (CG_add_5 cg x y d H) with x0:=x0 l:=l.
    Rewrite (cg_out_of_range_2 cg x H0 y H1). Reflexivity.
    Assumption.
  Qed.


Lemma cg_add_dom_subset : (cg:CGraph1) (x,y:ad) (d:D)
      (MapSubset ? ? (MapDom ? cg) (MapDom ? (CG_add cg x y d))).
  Proof.
    Unfold CG_add. Intros. Elim (option_sum ? (MapGet ? cg x)). Intro H. Elim H. Intros edges H0.
    Rewrite H0. Elim (option_sum ? (MapGet D edges y)). Intro H1. Elim H1. Intros d0 H2.
    Rewrite H2. Apply MapSubset_Dom_1. Apply MapSubset_Put.
    Intro H1. Rewrite H1. Apply MapSubset_Dom_1. Apply MapSubset_Put.
    Intro H. Rewrite H. Apply MapSubset_Dom_1. Apply MapSubset_Put.
  Qed.

(*s Adding a lis of adresses connected to [root] with weight $0$ *)

Fixpoint CG_add_root [root:ad; cg:CGraph1; l:(list ad)] : CGraph1 :=
    Cases l of
        nil => cg
	| (cons x l') => (CG_add_root root (CG_add cg root x Dz) l')
    end.

Lemma CG_add_root_out_of_range : (l:(list ad)) (cg:CGraph1) (root:ad)
    	((x0:ad) (d0:D) (l:(list ad)) (CG_path cg x0 d0 (cons x0 l)) -> (Dle Dz d0)=true) ->
    	(MapSubset ? ? (Elems l) (MapDom ? cg)) ->
	(ad_in_list root l)=false ->
	(in_dom ? root (cg_range cg))=false ->
	(x0:ad) (d0:D) (l0:(list ad)) (CG_path (CG_add_root root cg l) x0 d0 (cons x0 l0)) ->
	      (Dle Dz d0)=true.
    Proof.
    	Induction l. Trivial.
	Simpl. Intros. Apply (H (CG_add cg root a Dz) root) with x0:=x0 d0:=d0 l1:=l1. Intros.
    	Apply (cg_add_out_of_range_1 cg root a Dz) with x0:=x1 d0:=d1 l:=l2. Intros.
    	Exact (H0 ? ? ? H6).
	Assumption.
	Elim (orb_false_elim ? ? H2). Intros. Rewrite ad_eq_comm. Assumption.
	Assumption.
	Apply MapSubset_trans with m':=(MapPut unit (Elems l0) a tt). Apply MapSubset_Put.
	Apply MapSubset_trans with m':=(MapDom ? cg). Assumption.
	Apply cg_add_dom_subset.
	Elim (orb_false_elim ? ? H2). Trivial.
	Rewrite cg_range_4. Elim (orb_false_elim ? ? H2). Intros H5 H6. Rewrite H5. Rewrite H3.
    	Reflexivity.
	Assumption.
    Qed.

Lemma CG_add_rooted_1 : (cg:CGraph1) (root,a:ad) (d:D)
    	(CG_edge cg root a)=(NONE D) ->
    	  (CG_edge (CG_add cg root a d) root a)=(SOME D d).
  Proof.
    Intros. Change (CG_edge (cg2 cg root a d) root a)=(SOME D d). Rewrite CG_add_edge_1.
    Rewrite (ad_eq_correct root). Rewrite (ad_eq_correct a). Rewrite H. Reflexivity.
  Qed.

Lemma CG_add_root_rooted_1 : (l:(list ad)) (cg:CGraph1) (root,a:ad)
    	(ad_list_stutters l)=false ->
      (ad_in_list a l)=false -> (d:D) (CG_edge cg root a)=(SOME D d) ->
        (CG_edge (CG_add_root root cg l) root a)=(SOME D d).
  Proof.
    Induction l. Trivial.
    Simpl. Intros. Elim (orb_false_elim ? ? H0). Intros. Elim (orb_false_elim ? ? H1).
    Intros. Apply H. Assumption.
    Assumption.
    Change (CG_edge (cg2 cg root a Dz) root a0)=(SOME D d). Rewrite CG_add_edge_1.
    Rewrite (ad_eq_comm a a0). Rewrite H5. Rewrite (andb_b_false (ad_eq root root)). Assumption.
  Qed.

Lemma CG_add_root_rooted_2 : (l:(list ad)) (cg:CGraph1) (root:ad)
    	(ad_list_stutters l)=false ->
	((a0:ad) (ad_in_list a0 l)=true -> (CG_edge cg root a0)=(NONE D)) ->
    	(a:ad) (ad_in_list a l)=true ->
             (CG_edge (CG_add_root root cg l) root a)=(SOME ? Dz).
  Proof.
    Induction l. Intros. Discriminate H1.
    Simpl. Intros. Elim (orb_false_elim ? ? H0). Intros. Elim (sumbool_of_bool (ad_eq a0 a)).
    Intro H5. Rewrite (ad_eq_complete ? ? H5). Apply CG_add_root_rooted_1. Assumption.
    Assumption.
    Apply CG_add_rooted_1. Apply H1. Rewrite (ad_eq_correct a). Reflexivity.
    Intro H5. Rewrite H5 in H2. Simpl in H2. Apply H. Assumption.
    Intros. Change (CG_edge (cg2 cg root a Dz) root a1)=(NONE D). Rewrite CG_add_edge_1.
    Elim (sumbool_of_bool (ad_eq a a1)). Intro H7. Rewrite (ad_eq_complete ? ? H7) in H3.
    Rewrite H6 in H3. Discriminate H3.
    Intro H7. Rewrite H7. Rewrite (andb_b_false (ad_eq root root)).
    Apply H1. Rewrite H6. Apply orb_b_true.
    Assumption.
  Qed.
 
Lemma CG_add_root_rooted_3 : (cg:CGraph1) (root:ad)
	(in_dom ? root cg)=false ->
    	(a:ad) (in_dom ? a cg)=true ->
             (CG_edge (CG_add_root root cg (ad_list_of_dom ? cg)) root a)=(SOME ? Dz).
  Proof.
    Intros. Apply CG_add_root_rooted_2. Apply ad_list_of_dom_not_stutters.
    Intros. Unfold CG_edge. Rewrite (in_dom_none ? ? ? H). Reflexivity.
    Rewrite ad_in_list_of_dom_in_dom. Assumption.
  Qed.

Lemma CG_add_root_rooted_4 : (l:(list ad)) (cg:CGraph1) (root:ad) (a:ad)
    	(in_dom ? a (CG_add_root root cg l))=true -> {a=root}+{(in_dom ? a cg)=true}.
  Proof.
    Induction l. Intros. Right . Exact H.
    Simpl. Intros. Elim (H (CG_add cg root a Dz) root a0 H0). Intro H1. Left . Assumption.
    Intro H1. Unfold in_dom CG_add in H1. Elim (option_sum ? (MapGet ? cg root)). Intro H2.
    Elim H2. Intros edges H3. Rewrite H3 in H1. Elim (option_sum ? (MapGet D edges a)). Intro H4.
    Elim H4. Intros d H5. Rewrite H5 in H1.
    Rewrite (MapPut_semantics ? cg root (MapPut D edges a (Dmin Dz d)) a0) in H1.
    Elim (sumbool_of_bool (ad_eq root a0)). Intro H6. Left . Rewrite (ad_eq_complete ? ? H6).
    Reflexivity.
    Intro H6. Rewrite H6 in H1. Right . Exact H1.
    Intro H4. Rewrite H4 in H1.
    Rewrite (MapPut_semantics ? cg root (MapPut D edges a Dz) a0) in H1.
    Elim (sumbool_of_bool (ad_eq root a0)). Intro H5. Left . Rewrite (ad_eq_complete ? ? H5).
    Reflexivity.
    Intro H5. Rewrite H5 in H1. Right . Exact H1.
    Intro H2. Rewrite H2 in H1. Rewrite (MapPut_semantics ? cg root (M1 D a Dz) a0) in H1.
    Elim (sumbool_of_bool (ad_eq root a0)). Intro H3. Left . Rewrite (ad_eq_complete ? ? H3).
    Reflexivity.
    Intro H3. Rewrite H3 in H1. Right . Exact H1.
  Qed.

Lemma CG_edge_dist_some_1 : (n:nat) (cg:CGraph1) (x,y:ad) (d:D) (prefix:(list ad))
    	(CG_edge cg x y)=(SOME D d) -> (ad_in_list y prefix)=false ->
        {d':D | (Ddle (ad_simple_path_dist_1 cg x y prefix (S n)) (SOME ? d'))=true}.
  Proof.
    Unfold CG_edge. Intros. Simpl. Elim (sumbool_of_bool (ad_eq x y)). Intro H1. Rewrite H1.
    Split with Dz. Simpl. Apply Dle_refl.
    Intro H1. Rewrite H1. Elim (option_sum ? (MapGet ? cg x)). Intro H2. Elim H2.
    Intros edges H3. Rewrite H3 in H. Rewrite H3. Elim (option_sum ? (MapGet D edges y)).
    Intro H4. Elim H4. Intros d0 H5. Rewrite H5 in H. Inversion H. Split with (Dplus Dz d).
    Rewrite H7 in H5. Apply Ddle_trans with dd':=([z:ad] [d0:D]
            Case (orb (ad_eq z x) (ad_in_list z prefix)) of
               (NONE D)
               (Ddplus
                 (ad_simple_path_dist_1 cg z y (cons x prefix) n) d0)
               end y d).
    Apply all_min_le_1 with f:=[z:ad] [d0:D]
         Case (orb (ad_eq z x) (ad_in_list z prefix)) of
            (NONE D)
            (Ddplus (ad_simple_path_dist_1 cg z y (cons x prefix) n)
              d0)
            end.
    Assumption.
    Rewrite (ad_eq_comm y x). Rewrite H1. Rewrite H0. Simpl. Case n. Simpl.
    Rewrite (ad_eq_correct y). Apply Ddle_refl.
    Intro. Simpl. Rewrite (ad_eq_correct y). Apply Ddle_refl.
    Intro H4. Rewrite H4 in H. Discriminate H.
    Intro H2. Rewrite H2 in H. Discriminate H.
  Qed.

Lemma CG_edge_dist_some : (cg:CGraph1) (x,y:ad) (d:D)
    	(CG_edge cg x y)=(SOME D d) -> {d':D | (ad_simple_path_dist cg x y)=(SOME ? d')}.
  Proof.
    Intros. Elim (option_sum ? (ad_simple_path_dist cg x y)). Trivial.
    Unfold ad_simple_path_dist. Intro H0. Elim (option_sum ? (MapGet ? cg x)). Intro H1. Elim H1.
    Intros edges H2. Elim (MapCard_is_not_O ? cg x edges H2). Intros n H3.
    Elim (CG_edge_dist_some_1 n cg x y d (nil ad) H (refl_equal ? ?)). Intros d0 H4.
    Rewrite H3 in H0. Rewrite H0 in H4. Discriminate H4.
    Intro H1. Unfold CG_edge in H. Rewrite H1 in H. Discriminate H.
  Qed.

Lemma CG_add_root_rooted : (cg:CGraph1) (root:ad)
      ((x:ad) (d:D) (l:(list ad)) (CG_path cg x d (cons x l)) -> (Dle Dz d)=true) ->
 	(in_dom ? root cg)=false ->
    	(a:ad) (in_dom ? a (CG_add_root root cg (ad_list_of_dom ? cg)))=true ->
             (CG_leq (CG_add_root root cg (ad_list_of_dom ? cg)) root a)=true.
  Proof.
    Intros. Elim (CG_add_root_rooted_4 ? ? ? ? H1). Intro H2. Rewrite H2. Apply CG_leq_refl.
    Intro H2. Elim (CG_edge_dist_some ? root a Dz (CG_add_root_rooted_3 cg root H0 a H2)).
    Intros d H3. Unfold CG_leq. Rewrite H3. Reflexivity.
  Qed.

Lemma CG_add_sat : (cg:CGraph1) (root,a:ad) (d:D) (rho:ad->D)
    	(CGsat (cg2 cg root a d) rho) -> (CGsat cg rho).
  Proof.
    Unfold CGsat. Intros. Elim (sumbool_of_bool (andb (ad_eq root x) (ad_eq a y))). Intro H1.
    Apply Dle_trans with d':=(Dplus (rho y) (Dmin d d0)). Apply H. Rewrite CG_add_edge_1.
    Rewrite H1. Rewrite H0. Reflexivity.
    Apply Dle_plus_mono. Apply Dle_refl.
    Apply Dmin_le_2.
    Intro H1. Apply H. Rewrite CG_add_edge_1. Rewrite H1. Assumption.
  Qed.

Lemma CG_add_root_sat : (l:(list ad)) (cg:CGraph1) (root:ad) (rho:ad->D)
    	(CGsat (CG_add_root root cg l) rho) -> (CGsat cg rho).
  Proof.
    Induction l. Trivial.
    Simpl. Intros. Apply (CG_add_sat cg root a Dz rho). Unfold cg2. Exact (H ? ? ? H0).
  Qed.

Lemma CG_add_root_consistent : (l:(list ad)) (cg:CGraph1) (root:ad)
    	(CGconsistent (CG_add_root root cg l)) -> (CGconsistent cg).
  Proof.
    Unfold CGconsistent. Intros. Elim H. Intros rho H0. Split with rho.
    Exact (CG_add_root_sat l cg root rho H0).
  Qed.

Lemma CG_circuit_complete_1 : (cg:CGraph1)
    ((x:ad)(d:D)(l:(list ad))
     (CG_path cg x d (cons x l)) -> (Dle Dz d)=true) ->
     (root:ad) 
     root=(ad_alloc_opt unit (FSetUnion (MapDom ? cg) (MapDom ? (cg_range cg)))) ->
     (cg':CGraph1) cg'=(CG_add_root root cg (ad_list_of_dom ? cg)) 
  ->  (CGconsistent cg).
  Proof.
    Intros. Apply (CG_add_root_consistent (ad_list_of_dom (Map D) cg) cg root). Rewrite <- H1.
    Cut (orb (in_dom ? root cg) (in_dom ? root (cg_range cg)))=false. Intro H2.
    Elim (orb_false_elim ? ? H2). Intros. Elim CG_rooted_sat with cg:=cg' root:=root d0:=Dz.
    Intros rho H5. Elim H5. Unfold CGconsistent. Intros H6 H7. Split with rho. Assumption.
    Rewrite H1. Intros.
    Apply CG_add_root_out_of_range with l:=(ad_list_of_dom (Map D) cg) cg:=cg root:=root
                                        x0:=x d0:=d l0:=l.
    Assumption.
    Apply MapSubset_2_imp. Unfold MapSubset_2.
    Apply eqmap_trans with m':=(MapDomRestrBy unit unit (MapDom (Map D) cg) (MapDom (Map D) cg)).
    Apply MapDomRestrBy_ext. Apply Elems_of_list_of_dom.
    Apply eqmap_refl.
    Apply MapDomRestrBy_m_m_1.
    Rewrite ad_in_list_of_dom_in_dom. Assumption.
    Assumption.
    Assumption.
    Intros. Rewrite H1. Apply CG_add_root_rooted. Assumption.
    Assumption.
    Rewrite <- H1. Assumption.
    Rewrite MapDom_Dom. Rewrite MapDom_Dom. Rewrite <- in_FSet_union. Rewrite H0.
    Unfold in_FSet. Apply ad_alloc_opt_allocates.
  Qed.

(*s If there is no circuit [(cons x l)] with negative weight [d], then [cg] is consistent: *)

Theorem CG_circuit_complete : (cg:CGraph1)
      ((x:ad) (d:D) (l:(list ad)) (CG_path cg x d (cons x l)) -> (Dle Dz d)=true) ->
			          (CGconsistent cg).
  Proof.
    Intros. EApply CG_circuit_complete_1. Assumption.
    Reflexivity.
    Reflexivity.
  Qed.

Lemma CG_translate_l : (cg:CGraph1) (rho:ad->D) (d:D) (CGsat cg rho) ->
      (CGsat cg [a:ad] (Dplus d (rho a))).
  Proof.
    Unfold CGsat. Intros. Rewrite Dplus_assoc. Apply Dle_plus_mono. Apply Dle_refl.
    Apply H. Assumption.
  Qed.

(*s [(CGconsistent_anchored cg a d)] if there exists a valuation $\rho$ which 
     satisfies [cg] and such that $\rho(a)=d$
*)

Definition CGconsistent_anchored :=
      [cg:CGraph1][a:ad][d0:D] {rho:ad->D | (CGsat cg rho) /\ (rho a)=d0}.

Lemma CGconsistent_then_anchored 
  : (cg:CGraph1) (CGconsistent cg) ->
      (a:ad) (d0:D) (CGconsistent_anchored cg a d0).
  Proof.
    Unfold CGconsistent CGconsistent_anchored. Intros. Elim H. Intros rho H0.
    Split with [a0:ad](Dplus (Dplus d0 (Dneg (rho a))) (rho a0)). Split.
    Apply CG_translate_l. Assumption.
    Rewrite Dplus_assoc. Rewrite Dplus_neg_2. Apply Dplus_d_z.
  Qed.

Lemma CGanchored_then_consistent : (cg:CGraph1) (a:ad) (d0:D) (CGconsistent_anchored cg a d0) ->
      (CGconsistent cg).
  Proof.
    Unfold CGconsistent CGconsistent_anchored. Intros. Elim H. Intros rho H0. Elim H0. Intros.
    Split with rho. Assumption.
  Qed.

(*s Definition of [ad_0_path_dist_1] 
    a more efficient version of [ad_simple_path_dist]: *)

Section CGDist1.

    Variable cg : CGraph1.

Fixpoint ad_0_path_dist_1 [x,y:ad; l:(list ad); n:nat] : (option D) :=
      if (ad_eq x y)
      then (SOME ? Dz)
      else
      	Cases n of
	    O => (NONE ?)
	  | (S n') => Cases (MapGet ? cg x) of
	                  NONE => (NONE ?)
			| (SOME edges) =>
			  if (ad_in_list x l)
			  then (NONE D)
                          else let l'=(cons x l) in (* builds reverse path *)
			       (all_min [z:ad][d:D]
			           if (ad_in_list z l')
                                   then (NONE D)
				   else (Ddplus (ad_0_path_dist_1 z y l' n') d)
				   edges)
                      end
        end.

Definition ad_0_path_dist := [x,y:ad]
          (ad_0_path_dist_1 x y (nil ad) (MapCard ? cg)).

Lemma ad_0_path_dist_1_ge : (n:nat) (l:(list ad)) (x,y:ad)
      	(Ddle (ad_simple_path_dist_1 cg x y l n) (ad_0_path_dist_1 x y l n))=true.
    Proof.
      Induction n. Simpl. Intros. Apply Ddle_refl.
      Simpl. Intros. Case (ad_eq x y). Apply Ddle_refl.
      Case (MapGet ? cg x). Apply Ddle_refl.
      Intro. Case (ad_in_list x l). Apply Ddle_d_none.
      Apply all_min_le_3. Intros. Case (orb (ad_eq a x) (ad_in_list a l)). Apply Ddle_refl.
      Apply Ddle_plus_mono. Apply H.
      Apply Dle_refl.
    Qed.

Lemma ad_0_path_dist_1_correct_1 :
      	((x:ad) (d:D) (l:(list ad)) (CG_path cg x d (cons x l)) -> (Dle Dz d)=true) ->
        (n:nat) (x,y:ad) (l:(list ad)) (d:D)
    	  (le (length l) n) -> (CG_path cg y d (cons x l)) ->
      	  (prefix:(list ad))
      	    (ad_list_stutters (app (rev prefix) (cons x l)))=false ->
	      (Ddle (ad_0_path_dist_1 x y prefix n) (SOME ? d))=true.
    Proof.
      Induction n. Intros x y l. Case l. Intros. Simpl. 
      Inversion H1. Rewrite H5.
      Rewrite (ad_eq_correct y). Apply Ddle_refl.
      Intros. Elim (le_Sn_O ? H0).
      Intros n0 H0 x y l. Case l. Intros. Inversion H2. 
      Rewrite H6. Simpl.
      Rewrite (ad_eq_correct y). Rewrite H5. Apply Ddle_refl.
      Intros. Simpl. Elim (sumbool_of_bool (ad_eq x y)). Intro H4. Rewrite H4.
      Rewrite (ad_eq_complete ? ? H4) in H2. Exact (H ? ? ? H2).

      Intro H4. Rewrite H4. Elim (option_sum ? (MapGet ? cg x)). Intro H5. Elim H5.
      Intros edges H6. Rewrite H6. Inversion_clear H2. Apply Ddle_trans
             with dd':=Case (ad_in_list a (cons x prefix)) of
              (NONE D)
              (Ddplus (ad_0_path_dist_1 a y (cons x prefix) n0) d')
              end.
      Cut (MapGet ? edges a)=(SOME ? d'). Intro. Cut (ad_in_list x prefix)=false. Intro H9.
      Rewrite H9. Exact (all_min_le_1 [z:ad] [d:D]
          Case (orb (ad_eq z x) (ad_in_list z prefix)) of
             (NONE D)
             (Ddplus (ad_0_path_dist_1 z y (cons x prefix) n0) d)
             end edges a d' H2).
      Rewrite <- ad_in_list_rev. Exact (ad_list_stutters_prev_conv_l ? ? ? H3).
      Unfold CG_edge in H8. Rewrite H6 in H8. Elim (option_sum ? (MapGet D edges a)).
      Intro H9. Elim H9. Intros d1 H10. Rewrite H10 in H8. Rewrite H10. Assumption.
      Intro H9. Rewrite H9 in H8. Discriminate H8.
      Rewrite (ad_list_app_rev prefix (cons a l0) x) in H3.
      Rewrite <- (ad_in_list_rev (cons x prefix) a).
      Rewrite (ad_list_stutters_prev_conv_l ? ? ? H3).
      Apply (Ddle_plus_mono (ad_0_path_dist_1 a y (cons x prefix) n0) (SOME D d0) d' d').
      Exact (H0 a y l0 d0 (le_S_n ? ? H1) H7 (cons x prefix) H3).
      Apply Dle_refl.
      Intro H5. Inversion H2.
      Unfold CG_edge in H11. Rewrite H5 in H11. Discriminate H11.
    Qed.

Lemma ad_0_path_dist_1_le :
      	((x:ad) (d:D) (l:(list ad)) (CG_path cg x d (cons x l)) -> (Dle Dz d)=true) ->
	(n:nat) (x,y:ad)
      	  (Ddle (ad_0_path_dist_1 x y (nil ad) n) (ad_simple_path_dist_1 cg x y (nil ad) n))=true.
    Proof.
      Intros. Elim (option_sum ? (ad_simple_path_dist_1 cg x y (nil ad) n)). Intro H0. Elim H0.
      Intros d H1. Rewrite H1.
      Elim (ad_simple_path_dist_1_complete_1 cg n x y (nil ad) Dz) with d0:=d. Intros l H2.
      Elim H2. Intros H3 H4. Apply (ad_0_path_dist_1_correct_1 H n x y l). Exact (proj2 ? ? H4).
      Rewrite (Dplus_d_z d) in H3. Exact H3.
      Exact (proj1 ? ? H4).
      Simpl. Apply CG_p1. Reflexivity.
      Reflexivity.
      Assumption.
      Intro H0. Rewrite H0. Apply Ddle_d_none.
    Qed.

Lemma ad_0_path_dist_correct_1 :
      	(CGconsistent cg) ->
	(x,y:ad) (n:nat)
	  (ad_0_path_dist_1 x y (nil ad) n)=(ad_simple_path_dist_1 cg x y (nil ad) n).
    Proof.
      Intros. Apply Ddle_antisym. Apply ad_0_path_dist_1_le.
      Exact (CG_circuits_non_negative_weight cg H).
      Apply ad_0_path_dist_1_ge.
    Qed.

Lemma ad_0_path_dist_correct : (CGconsistent cg) ->
      	(x,y:ad) (ad_0_path_dist x y)=(ad_simple_path_dist cg x y).
    Proof.
      Intros. Exact (ad_0_path_dist_correct_1 H x y (MapCard ? cg)).
    Qed.

(*s Uses a set [s] of already visited nodes *)

Fixpoint ad_1_path_dist_1 [x,y:ad; s:FSet; n:nat] : (option D) :=
      if (ad_eq x y)
      then (SOME ? Dz)
      else
      	Cases n of
	    O => (NONE ?)
	  | (S n') => Cases (MapGet ? cg x) of
	                  NONE => (NONE ?)
			| (SOME edges) =>
			  Cases (MapGet ? s x) of
			      (SOME _) => (NONE ?)
			    | NONE => let s'=(MapPut unit s x tt) in
			              (all_min [z:ad][d:D]
			                  Cases (MapGet ? s' z) of
				              (SOME _) => (NONE D)
				            | NONE => (Ddplus (ad_1_path_dist_1 z y s' n') d)
				          end
				          edges)
                          end
	              end
        end.

Definition ad_1_path_dist := [x,y:ad]
          (ad_1_path_dist_1 x y (M0 unit) (MapCard ? cg)).

Lemma ad_1_path_dist_correct_1 : (n:nat) (x,y:ad) (l:(list ad))
      	  (ad_1_path_dist_1 x y (Elems l) n)=(ad_0_path_dist_1 x y l n).
    Proof.
      Induction n. Trivial.
      Simpl. Intros. Case (ad_eq x y). Reflexivity.
      Case (MapGet ? cg x). Reflexivity.
      Intro. Unfold all_min. Elim (sumbool_of_bool (ad_in_list x l)). Intro H0. Rewrite H0.
      Rewrite <- (ad_in_elems_in_list l x) in H0. Elim (in_dom_some ? ? ? H0). Intros t H1.
      Rewrite H1. Reflexivity.
      Intro H0. Rewrite H0. Rewrite <- (ad_in_elems_in_list l x) in H0.
      Rewrite (in_dom_none ? ? ? H0). Apply MapFold_ext_f. Intros.
      Elim (sumbool_of_bool (ad_in_list a (cons x l))). Intro H2.
      Rewrite <- (ad_in_elems_in_list (cons x l) a) in H2. Elim (in_dom_some ? ? ? H2). Simpl.
      Intro t. Elim t. Intro H3. Rewrite H3. Rewrite (ad_in_elems_in_list (cons x l) a) in H2.
      Simpl in H2. Rewrite H2. Reflexivity.
      Intro H2. Cut (orb (ad_eq a x) (ad_in_list a l))=false. Intro H3. Rewrite H3.
      Rewrite <- (ad_in_elems_in_list (cons x l) a) in H2. Simpl in H2.
      Rewrite (in_dom_none ? ? ? H2). Rewrite <- (H a y (cons x l)). Reflexivity.
      Assumption.
    Qed.

Lemma ad_1_path_dist_correct_2 : (x,y:ad) (ad_1_path_dist x y)=(ad_0_path_dist x y).
    Proof.
      Intros. Exact (ad_1_path_dist_correct_1 (MapCard ? cg) x y (nil ad)).
    Qed.

Lemma ad_1_path_dist_correct_3 : (CGconsistent cg) ->
      	(n:nat) (x,y:ad)
          (ad_1_path_dist_1 x y (M0 unit) n)=(ad_simple_path_dist_1 cg x y (nil ad) n).
    Proof.
      Intros. Rewrite <- (ad_0_path_dist_correct_1 H x y n).
      Exact (ad_1_path_dist_correct_1 n x y (nil ad)).
    Qed.

Lemma ad_1_path_dist_correct : (CGconsistent cg) ->
      	(x,y:ad) (ad_1_path_dist x y)=(ad_simple_path_dist cg x y).
    Proof.
      Intros. Rewrite ad_1_path_dist_correct_2. Apply ad_0_path_dist_correct. Assumption.
    Qed.

Lemma ad_1_path_dist_big_enough_1 : (n:nat) (s:FSet)
      	(MapSubset ? ? s (MapDom ? cg)) ->
      	(le (MapCard ? cg) (plus n (MapCard ? s))) ->
	  (x,y:ad) (ad_1_path_dist_1 x y s n)=(ad_1_path_dist_1 x y s (S n)).
    Proof.
      Induction n. Intros. Simpl. Case (ad_eq x y). Reflexivity.
      Elim (sumbool_of_bool (in_dom ? x cg)). Intro H1. Elim (in_dom_some ? ? ? H1).
      Intros edges H2. Rewrite H2. Elim (sumbool_of_bool (in_dom ? x s)). Intro H3.
      Elim (in_dom_some ? ? ? H3). Intros t H4. Rewrite H4. Reflexivity.
      Intro H3. Simpl in H0. Rewrite (MapCard_Dom ? cg) in H0. Rewrite (MapDom_Dom ? s x) in H3.
      Cut (MapGet ? (MapDom unit s) x)=(NONE ?). Rewrite (MapSubset_card_eq ? ? ? ? H H0 x).
      Rewrite (FSet_Dom (MapDom ? cg)).
      Elim (in_dom_some ? ? ? (MapDom_semantics_1 ? cg x edges H2)). Intros t H4 H5.
      Rewrite H4 in H5. Discriminate H5.
      Exact (in_dom_none ? ? ? H3).
      Intro H1. Rewrite (in_dom_none ? ? ? H1). Reflexivity.
      Intros. Cut (m:nat) m=(S n0)->(ad_1_path_dist_1 x y s (S n0))=(ad_1_path_dist_1 x y s (S m)).
      Intro. Exact (H2 (S n0) (refl_equal ? ?)).
      Intros. Simpl. Case (ad_eq x y). Reflexivity.
      Elim (option_sum ? (MapGet ? cg x)). Intro H'. Elim H'. Intros edges H'0. Rewrite H'0.
      Elim (option_sum ? (MapGet ? s x)). Intro H3. Elim H3. Intros t H4. Rewrite H4. Reflexivity.
      Intro H3. Rewrite H3. Unfold all_min. Apply MapFold_ext_f. Intros.
      Rewrite (MapPut_semantics unit s x tt a). Elim (sumbool_of_bool (ad_eq x a)). Intro H5.
      Rewrite H5. Reflexivity.
      Intro H5. Rewrite H5. Case (MapGet ? s a). Rewrite H2. Rewrite H. Reflexivity.
      Unfold MapSubset. Intros. Elim (in_dom_some ? ? ? H6). Intro.
      Rewrite (MapPut_semantics unit s x tt a0). Elim (sumbool_of_bool (ad_eq x a0)). Intro H7.
      Rewrite H7. Intro H8. Rewrite <- (ad_eq_complete ? ? H7). Fold (in_FSet x (MapDom ? cg)).
      Rewrite <- (MapDom_Dom ? cg x). Unfold in_dom. Rewrite H'0. Reflexivity.
      Intro H7. Rewrite H7. Intro H8. Apply (H0 a0). Unfold in_dom. Rewrite H8. Reflexivity.
      Rewrite MapCard_Put_2_conv. Rewrite <- plus_Snm_nSm. Exact H1.
      Assumption.
      Trivial.
      Intro H3. Rewrite H3. Reflexivity.
    Qed.

Lemma ad_1_path_dist_big_enough_2 : (n:nat)
	  (x,y:ad) (ad_1_path_dist x y)=(ad_1_path_dist_1 x y (M0 unit) (plus n (MapCard ? cg))).
    Proof.
      Induction n. Trivial.
      Intros. Unfold plus. Fold (plus n0 (MapCard ? cg)). Rewrite <- ad_1_path_dist_big_enough_1.
      Apply H.
      Unfold MapSubset. Intros. Discriminate H0.
      Simpl. Rewrite <- plus_n_O. Apply le_plus_r.
    Qed.

Lemma ad_1_path_dist_big_enough : (n:nat) (le (MapCard ? cg) n) ->
	  (x,y:ad) (ad_1_path_dist x y)=(ad_1_path_dist_1 x y (M0 unit) n).
    Proof.
      Intros. Cut (EX m:nat | n=(plus m (MapCard ? cg))). Intro H0. Elim H0. Intros m H1.
      Rewrite H1. Apply ad_1_path_dist_big_enough_2.
      Elim H. Split with O. Reflexivity.
      Intros. Elim H1. Intros m' H2. Split with (S m'). Rewrite H2. Reflexivity.
    Qed.

End CGDist1.

(*s Definition of concrete formulas : 
    [(CGleq x y d)] means $x\leq y+d$, [(CGeq x y d)] means $x=y+d$
 *)

Inductive CGForm : Set :=
      CGleq : ad -> ad -> D -> CGForm 
    | CGeq : ad -> ad -> D -> CGForm  
    | CGand : CGForm -> CGForm -> CGForm
    | CGor : CGForm -> CGForm -> CGForm
    | CGimp : CGForm -> CGForm -> CGForm
    | CGnot : CGForm -> CGForm.

(*s Interpretation of concrete formulas as proposition *)

Fixpoint CGeval [rho:ad->D; f:CGForm] : Prop :=
    Cases f of
        (CGleq x y d) => (Dle (rho x) (Dplus (rho y) d))=true
      | (CGeq x y d) => (rho x)=(Dplus (rho y) d)
      | (CGand f0 f1) => (CGeval rho f0) /\ (CGeval rho f1)
      | (CGor f0 f1) => (CGeval rho f0) \/ (CGeval rho f1)
      | (CGimp f0 f1) => (CGeval rho f0) -> (CGeval rho f1)
      | (CGnot f0) => ~(CGeval rho f0)
    end.

(*s Decidability of satisfaction *)

Lemma CGeval_dec : (f:CGForm) (rho:ad->D) {(CGeval rho f)}+{~(CGeval rho f)}.
  Proof.
    Induction f. 
    Intros. Simpl. Elim (sumbool_of_bool (Dle (rho a) (Dplus (rho a0) d))).
    Intro H. Left . Assumption.
    Intro H. Right . Unfold not. Rewrite H. Intro H0. Discriminate H0.
    Simpl. Intros. Apply D_dec.
    Simpl. Intros. Elim (H rho). Intro H1. Elim (H0 rho). Intro H2. Left . (Split; Assumption).
    Unfold not. Intro H2. Right . Intro. Elim H3. Intro. Assumption.
    Unfold not. Intro H1. Right . Intro H2. Elim H2. Intros. Apply (H1 H3).
    Simpl. Intros. Elim (H rho). Intro H1. Left . Left . Assumption.
    Elim (H0 rho). Intros H1 H2. Left . Right . Assumption.
    Unfold not. Intros H1 H2. Right . Intro H3. (Elim H3; Assumption).
    Simpl. Intros. Elim (H0 rho). Intro H1. Left . Intro H2. Assumption.
    Elim (H rho). Unfold not. Intros H1 H2. Right . Intro H3. Apply H2. Apply H3. Assumption.
    Unfold not. Intros H1 H2. Left . Intro H3. Elim (H1 H3).
    Intros. Simpl. Elim (H rho). Intro H0. Right . Unfold not. Intros. Exact (H1 H0).
    Intro H0. Left . Assumption.
  Qed.

(*s Simplified formulae: *)
Inductive CGSForm : Set :=
      CGSleq : ad -> ad -> D -> CGSForm
    | CGSand : CGSForm -> CGSForm -> CGSForm
    | CGSor : CGSForm -> CGSForm -> CGSForm.

Fixpoint CG_of_CGS [fs:CGSForm] : CGForm :=
    Cases fs of
        (CGSleq x y d) => (CGleq x y d)
      | (CGSand fs0 fs1) => (CGand (CG_of_CGS fs0) (CG_of_CGS fs1))
      | (CGSor fs0 fs1) => (CGor (CG_of_CGS fs0) (CG_of_CGS fs1))
    end.

Definition CGSeval := [rho:ad->D; fs:CGSForm] (CGeval rho (CG_of_CGS fs)).

(*s Decision procedure for simplified formulae *)

Section CGSSolve.

    Variable anchor : ad.
    Variable anchor_value : D.

(*s Is $x\leq y+d$ consistent with [cg]? *)

Definition CG_test_ineq := [cg:CGraph1; n:nat; x,y:ad; d:D]
      	(Ddle (SOME ? (Dneg d)) (ad_1_path_dist_1 cg y x (M0 unit) n)).

    Variable def_answer : bool.

(*s Invariants: [cg] is consistent, [|cg|<=n].
       [(CGS_solve_1 cg n fsl gas)]
       returns [true] iff [cg /\ fsl /\ anchor=anchor_value] is consistent,
       	 where [fsl] is understood as the conjunction of all the [fs] in [fsl];
         i.e. iff [cg /\ fsl] alone is consistent 
          (lemmas [CG_anchored_then_consistent] and [CG_consistent_then_anchored)].
       [gas] is intended to be [>=] the sum of sizes of all formulas in [fsl]. *)

Fixpoint CGS_solve_1 [cg:CGraph1; n:nat; fsl:(list CGSForm); gas:nat] : bool :=
      Cases gas of
          O => def_answer
	| (S gas') =>
          Cases fsl of
              nil => true
	    | (cons fs fsl') =>
              Cases fs of
                  (CGSleq x y d) => if (CG_test_ineq cg n x y d)
                                    then let cg' = (CG_add cg x y d) in 
                                             (CGS_solve_1 cg' (S n) fsl' gas')
		                    else false
                | (CGSand fs0 fs1) => (CGS_solve_1 cg n (cons fs0 (cons fs1 fsl')) gas')
	        | (CGSor fs0 fs1) => if (CGS_solve_1 cg n (cons fs0 fsl') gas')
	                             then true
			             else (CGS_solve_1 cg n (cons fs1 fsl') gas')
              end
          end
      end.

(*s Size of a set of formula and of a list of formula *)

Fixpoint FSize [f:CGSForm] : nat :=
      Cases f of
          (CGSand f0 f1) => (S (plus (FSize f0) (FSize f1)))
	| (CGSor f0 f1) => (S (plus (FSize f0) (FSize f1)))
	| _ => (1)
      end.

Fixpoint FlSize [fsl:(list CGSForm)] : nat :=
      Cases fsl of
          nil => O
	| (cons fs fsl') => (plus (FSize fs) (FlSize fsl'))
      end.


Definition CGS_solve := [fs:CGSForm] (CGS_solve_1 (M0 ?) O (cons fs (nil ?)) (S (FSize fs))).

(*s Interpretation of a list of formula as a conjonction *)

Fixpoint CGSeval_l [rho:ad->D; fsl:(list CGSForm)] : Prop :=
      Cases fsl of
          nil => True
	| (cons fs fsl') => (CGSeval rho fs) /\ (CGSeval_l rho fsl')
      end.

Lemma FSize_geq_1 : (fs:CGSForm) {n:nat | (FSize fs)=(S n)}.
    Proof.
      Induction fs. Simpl. Intros. Split with O. Reflexivity.
      Intros. Simpl. Split with (plus (FSize c) (FSize c0)). Reflexivity.
      Intros. Simpl. Split with (plus (FSize c) (FSize c0)). Reflexivity.
    Qed.

Lemma FlSize_is_O : (fsl:(list CGSForm)) (FlSize fsl)=O -> fsl=(nil ?).
    Proof.
      Induction fsl. Trivial.
      Intros. Simpl in H0. Elim (FSize_geq_1 a). Intros n H1. Rewrite H1 in H0. Discriminate H0.
    Qed.

Lemma CG_add_card_le : (cg:CGraph1) (x,y:ad) (d:D) (n:nat)
      	(le (MapCard ? cg) n) -> (le (MapCard ? (CG_add cg x y d)) (S n)).
    Proof.
      Intros. Unfold CG_add. Case (MapGet ? cg x).
      Apply (le_trans ? ? (S n) (MapCard_Put_ub ? cg x (M1 D y d))). Apply le_n_S. Assumption.
      Intro. Case (MapGet ? m y).
      Apply (le_trans ? ? (S n) (MapCard_Put_ub ? cg x (MapPut D m y d))). Apply le_n_S.
      Assumption.
      Intro. Apply (le_trans ? ? (S n) (MapCard_Put_ub ? cg x (MapPut D m y (Dmin d d0)))).
      Apply le_n_S. Assumption.
    Qed.

Lemma CGS_solve_1_correct : (gas:nat) (fsl:(list CGSForm)) (cg:CGraph1) (n:nat)
      	(CGconsistent cg) ->
      	(le (MapCard ? cg) n) ->
	(lt (FlSize fsl) gas) ->
	(CGS_solve_1 cg n fsl gas)=true ->
	  {rho:ad->D | (CGSeval_l rho fsl) /\ (CGsat cg rho)}.
    Proof.
      Induction gas. Intros. Elim (lt_n_O ? H1).
      Simpl. Intros n H fsl. Case fsl. Intros. Elim H0. Intros rho H4. Split with rho.
      Split. Exact I.
      Assumption.
      Intro fs. Case fs. Intros. Elim (sumbool_of_bool (CG_test_ineq cg n0 a a0 d)). Intro H4.
      Rewrite H4 in H3. Unfold CG_test_ineq in H4. Elim (H l (CG_add cg a a0 d) (S n0)).
      Intros rho H5. Split with rho. Elim H5. Intros. Split. Simpl. Split. Unfold CGSeval.
      Simpl. Exact (CG_add_3 cg a a0 d rho H7).
      Assumption.
      Exact (CG_add_2 cg a a0 d rho H7).
      Apply CG_circuit_complete. 
      Rewrite <- (ad_1_path_dist_big_enough cg n0 H1 a0 a) in H4.
      Rewrite (ad_1_path_dist_correct cg H0 a0 a) in H4.
      Exact (CG_add_5 cg a a0 d (CG_circuits_non_negative_weight cg H0) H4).
      Apply CG_add_card_le. Assumption.
      Exact (lt_S_n ? ? H2).
      Assumption.
      Intro H4. Rewrite H4 in H3. Discriminate H3.
      Intros. Elim (H (cons c (cons c0 l)) cg n0 H0). Simpl. Intros rho H4. Split with rho.
      Elim H4. Intros. Split; Try Assumption. Elim H5. Intros. Elim H8. Intros.
      Split; Try Assumption. Exact (conj ? ? H7 H9).
      Assumption.
      Simpl. Simpl in H2. Rewrite plus_assoc_l. Apply lt_S_n. Assumption.
      Assumption.
      Intros. Elim (sumbool_of_bool (CGS_solve_1 cg n0 (cons c l) n)). Intro H4.
      Elim (H (cons c l) cg n0 H0 H1). Intros rho H5. Split with rho. Elim H5. Intros. Simpl.
      Split; Try Assumption. Split; Try Assumption. Unfold CGSeval. Simpl. Left . Simpl in H6.
      Exact (proj1 ? ? H6).
      Exact (proj2 ? ? H6).
      Simpl. Simpl in H2. Apply le_lt_trans with m:=(plus (plus (FSize c) (FSize c0)) (FlSize l)).
      Apply le_reg_r. Apply le_plus_l.
      Apply lt_S_n. Assumption.
      Assumption.
      Intro H4. Rewrite H4 in H3. Elim (H (cons c0 l) cg n0 H0). Intros rho H5. Elim H5.
      Intros. Split with rho. Split; Try Assumption. Simpl. Simpl in H6. Elim H6. Intros.
      Split; Try Assumption. Unfold CGSeval. Simpl. Right . Assumption.
      Assumption.
      Simpl. Simpl in H2. Apply le_lt_trans with m:=(plus (plus (FSize c) (FSize c0)) (FlSize l)).
      Apply le_reg_r. Apply le_plus_r.
      Apply lt_S_n. Assumption.
      Assumption.
    Qed.

Lemma CGS_solve_correct : (fs:CGSForm) (CGS_solve fs)=true ->
          {rho:ad->D | (CGSeval rho fs)}.
    Proof.
      Intros. Elim (CGS_solve_1_correct (S (FSize fs)) (cons fs (nil ?)) (M0 ?) O). Intros rho H0.
      Simpl in H0. Elim H0. Intros. Elim H1. Intros. Split with rho. Assumption.
      Split with [x:ad]Dz. Unfold CGsat. Unfold CG_edge. Simpl. Intros. Discriminate H0.
      Apply le_n.
      Simpl. Rewrite <- plus_n_O. Unfold lt. Apply le_n.
      Exact H.
    Qed.

Lemma CGS_translate_l : (fs:CGSForm) (rho:ad->D) (d:D) (CGSeval rho fs) ->
      	(CGSeval [a:ad] (Dplus d (rho a)) fs).
    Proof.
      Induction fs. Unfold CGSeval. Simpl. Intros. Rewrite Dplus_assoc. Apply Dle_plus_mono.
      Apply Dle_refl.
      Assumption.
      Unfold CGSeval. Simpl. Intros. Elim H1. Intros. Split. Apply H. Assumption.
      Apply H0. Assumption.
      Unfold CGSeval. Simpl. Intros. Elim H1. Intro. Left . Apply H. Assumption.
      Intro. Right . Apply H0. Assumption.
    Qed.

Lemma CGS_solve_correct_anchored : (fs:CGSForm) (CGS_solve fs)=true ->
          {rho:ad->D | (CGSeval rho fs) /\ (rho anchor)=anchor_value}.
    Proof.
      Intros. Elim (CGS_solve_correct fs H). Intros rho H0.
      Split with [a:ad](Dplus (Dplus anchor_value (Dneg (rho anchor))) (rho a)). Split.
      Apply CGS_translate_l. Assumption.
      Rewrite Dplus_assoc. Rewrite Dplus_neg_2. Apply Dplus_d_z.
    Qed.

Lemma CGS_solve_complete_1 : (gas:nat) (fsl:(list CGSForm)) (cg:CGraph1) (n:nat)
        (lt (FlSize fsl) gas) -> (le (MapCard ? cg) n) ->
      	  (rho:ad->D) (CGsat cg rho) -> (CGSeval_l rho fsl) -> (CGS_solve_1 cg n fsl gas)=true.
    Proof.
      Induction gas. Intros. Elim (lt_n_O ? H).
      Intros n H fsl. Case fsl. Trivial.
      Intro fs. Case fs. Simpl. Intros. Unfold CG_test_ineq.
      Rewrite <- (ad_1_path_dist_big_enough cg n0 H1 a0 a). Cut (CGconsistent cg). Intro H4.
      Rewrite (ad_1_path_dist_correct cg H4 a0 a). Elim H3. Intros.
      Rewrite (CG_sat_add_1 cg a a0 d rho H2 H5). Apply H with rho:=rho. Apply lt_S_n. Assumption.
      Apply CG_add_card_le. Assumption.
      Fold (cg2 cg a a0 d). Apply CG_add_1. Assumption.
      Exact H5.
      Assumption.
      Split with rho. Assumption.
      Simpl. Intros. Apply H with rho:=rho. Simpl. Rewrite plus_assoc_l. Apply lt_S_n. Assumption.
      Assumption.
      Assumption.
      Elim H3. Intros. Simpl. Elim H4. Intros. Split; Try Assumption. Split; Assumption.
      Simpl. Intros. Elim H3. Intros. Elim H4. Intro. Cut (CGS_solve_1 cg n0 (cons c l) n)=true.
      Intro H7. Rewrite H7. Reflexivity.
      Apply H with rho:=rho. Simpl.
      Apply le_lt_trans with m:=(plus (plus (FSize c) (FSize c0)) (FlSize l)). Apply le_reg_r.
      Apply le_plus_l.
      Apply lt_S_n. Assumption.
      Assumption.
      Assumption.
      Split; Assumption.
      Intro H6. Cut (CGS_solve_1 cg n0 (cons c0 l) n)=true. Intro H7.
      Case (CGS_solve_1 cg n0 (cons c l) n); Trivial.
      Apply H with rho:=rho. Simpl.
      Apply le_lt_trans with m:=(plus (plus (FSize c) (FSize c0)) (FlSize l)). Apply le_reg_r.
      Apply le_plus_r.
      Apply lt_S_n. Assumption.
      Assumption.
      Assumption.
      Split; Assumption.
    Qed.

Lemma CGS_solve_complete : (fs:CGSForm) (rho:ad->D)
        (CGSeval rho fs) -> (CGS_solve fs)=true.
    Proof.
      Intros. Apply (CGS_solve_complete_1 (S (FSize fs)) (cons fs (nil ?)) (M0 ?) O) with rho:=rho.
      Simpl. Rewrite <- plus_n_O. Unfold lt. Apply le_n.
      Apply le_n.
      Unfold CGsat. Intros. Unfold CG_edge in H0. Discriminate H0.
      Simpl. Split; Trivial.
    Qed.

Definition CGSeq := [x,y:ad] [d:D] (CGSand (CGSleq x y d) (CGSleq y x (Dneg d))).

Lemma CGSeq_correct : (x,y:ad) (d:D) (rho:ad->D)
      	(CGSeval rho (CGSeq x y d)) -> (rho x)=(Dplus (rho y) d).
    Proof.
      Intros. Unfold CGSeq CGSeval in H. Simpl in H. Elim H. Intros. Apply Dle_antisym. Assumption.
      Apply Dplus_reg_r with d'':=(Dneg d). Rewrite Dplus_assoc. Rewrite Dplus_neg.
      Rewrite Dplus_d_z. Assumption.
    Qed.

Lemma CGSeq_complete : (x,y:ad) (d:D) (rho:ad->D)
      	(rho x)=(Dplus (rho y) d) -> (CGSeval rho (CGSeq x y d)).
    Proof.
      Intros. Unfold CGSeq CGSeval. Simpl. Rewrite H. Split. Apply Dle_refl.
      Rewrite Dplus_assoc. Rewrite Dplus_neg. Rewrite Dplus_d_z. Apply Dle_refl.
    Qed.

End CGSSolve.

Section CGWithOne.

    Variable Done : D.
    Variable Done_pos : (Dle Done Dz)=false.
    Variable Done_min_pos : (d:D) (Dle d Dz)=false -> (Dle Done d)=true.

(*s Defining the negation of a formula :
	  $\neg x \leq y+d \Leftrightarrow x>y+d \Leftrightarrow x \geq y+d+1$
 *)
Fixpoint CGSnot [fs:CGSForm] : CGSForm :=
      Cases fs of
      	  (CGSleq x y d) => (CGSleq y x (Dneg (Dplus d Done)))

	| (CGSand f0 f1) => (CGSor (CGSnot f0) (CGSnot f1))
	| (CGSor f0 f1) => (CGSand (CGSnot f0) (CGSnot f1))
      end.

Lemma Dmone_neg : (Dle Dz (Dneg Done))=false.
    Proof.
      Elim (sumbool_of_bool (Dle Dz (Dneg Done))). Intro H. 
      Rewrite <- (Dneg_neg Done) in Done_pos.
      Rewrite (Dle_neg ? H) in Done_pos. Discriminate Done_pos.
      Trivial.
    Qed.

Lemma Dminus_one_1 : (d:D) (Dle d (Dplus d (Dneg Done)))=false.
    Proof.
      Intro. Elim (sumbool_of_bool (Dle d (Dplus d (Dneg Done)))). Intro H.
      Cut (Dle Dz (Dneg Done))=true. Intro. Rewrite Dmone_neg in H0. Discriminate H0.
      Apply Dplus_reg_l with d'':=d. Rewrite Dplus_d_z. Assumption.
      Trivial.
    Qed.

Lemma Dle_lt_1 : (d,d':D) (Dle d' d)=false -> (Dle d (Dplus d' (Dneg Done)))=true.
    Proof.
      Intros. Apply Dplus_reg_r with d'':=Done. Rewrite Dplus_assoc. Rewrite Dplus_neg_2.
      Rewrite Dplus_d_z. Apply Dplus_reg_l with d'':=(Dneg d). Rewrite <- Dplus_assoc.
      Rewrite Dplus_neg_2. Rewrite Dplus_z_d. Apply Done_min_pos.
      Elim (sumbool_of_bool (Dle (Dplus (Dneg d) d') Dz)). Intro H0. Cut (Dle d' d)=true.
      Rewrite H. Intro. Discriminate H1.
      Apply Dplus_reg_l with d'':=(Dneg d). Rewrite Dplus_neg_2. Assumption.
      Trivial.
    Qed.

Lemma Dle_lt_2 : (d,d':D) (Dle d (Dplus d' (Dneg Done)))=true -> (Dle d' d)=false.
    Proof.
      Intros. Elim (sumbool_of_bool (Dle d' d)). Intro H0. Cut (Dle d (Dplus d (Dneg Done)))=true.
      Rewrite Dminus_one_1. Intro. Discriminate H1.
      Apply Dle_trans with d':=(Dplus d' (Dneg Done)). Assumption.
      Apply Dle_plus_mono. Assumption.
      Apply Dle_refl.
      Trivial.
    Qed.

Lemma CGSnot_correct : (fs:CGSForm) (rho:ad->D) (CGSeval rho fs) -> ~(CGSeval rho (CGSnot fs)).
    Proof.
      Unfold not. Induction fs. Simpl. Unfold CGSeval. Simpl. Intros.
      Cut (Dle (rho a) (Dplus (rho a) (Dneg Done)))=true. Rewrite Dminus_one_1. Intro.
      Discriminate H1.
      Rewrite <- (Dplus_d_z (Dneg Done)). Rewrite <- (Dplus_neg_2 d).
      Rewrite <- (Dplus_assoc (Dneg Done)). Rewrite <- Dneg_plus.
      Apply Dle_trans with d':=(Dplus (rho a0) d). Assumption.
      Rewrite <- Dplus_assoc. Apply Dle_plus_mono. Assumption.
      Apply Dle_refl.
      Unfold CGSeval. Simpl. Intros. Elim H1. Intros. Elim H2. Intro. Exact (H rho H3 H5).
      Intro. Exact (H0 rho H4 H5).
      Unfold CGSeval. Simpl. Intros. Elim H2. Intros. Elim H1. Intro. Exact (H rho H5 H3).
      Intro. Exact (H0 rho H5 H4).
    Qed.

Lemma CGSnot_complete : (fs:CGSForm) (rho:ad->D)
        ~(CGSeval rho (CGSnot fs)) -> (CGSeval rho fs).
    Proof.
      Unfold not CGSeval. Induction fs. Simpl. Intros.
      Elim (sumbool_of_bool (Dle (rho a) (Dplus (rho a0) d))). Trivial.
      Intro H0. Cut False. Intro. Elim H1.
      Apply H. Rewrite Dneg_plus. Rewrite <- Dplus_assoc. Apply Dplus_reg_r with d'':=d.
      Rewrite Dplus_assoc. Rewrite Dplus_neg_2. Rewrite Dplus_d_z. Apply Dle_lt_1. Assumption.
      Simpl. Intros. Split. Apply H. Intro. Apply H1. Left . Assumption.
      Apply H0. Intro. Apply H1. Right . Assumption.
      Simpl. Intros.
      Cut ~(CGeval rho (CG_of_CGS (CGSnot c))) \/ ~(CGeval rho (CG_of_CGS (CGSnot c0))). Intro.
      Elim H2. Intro. Left . Apply H. Assumption.
      Intro. Right . Apply H0. Assumption.
      Elim (CGeval_dec (CG_of_CGS (CGSnot c)) rho). Intro H2.
      Elim (CGeval_dec (CG_of_CGS (CGSnot c0)) rho). Intro H3. Elim (H1 (conj ? ? H2 H3)).
      Intro H3. Right . Assumption.
      Intro H2. Left . Assumption.
    Qed.

(*s Interpreting formula as simplified formula *)

Fixpoint CGFormSimplify [f:CGForm] : CGSForm :=
      Cases f of
          (CGleq x y d) => (CGSleq x y d)
        | (CGeq x y d) => (CGSeq x y d)
        | (CGand f0 f1) => (CGSand (CGFormSimplify f0) (CGFormSimplify f1))
        | (CGor f0 f1) => (CGSor (CGFormSimplify f0) (CGFormSimplify f1))
        | (CGimp f0 f1) => (CGSor (CGSnot (CGFormSimplify f0)) (CGFormSimplify f1))
        | (CGnot f0) => (CGSnot (CGFormSimplify f0))
      end.

Lemma  CGFormSimplify_correct : (f:CGForm) (rho:ad->D)
        (CGeval rho f) <-> (CGSeval rho (CGFormSimplify f)).
    Proof.
      Induction f. Intros. Split; Trivial.
      Intros. Unfold CGSeval. Simpl. Split. Intro H. Exact (CGSeq_complete a a0 d rho H).
      Exact (CGSeq_correct a a0 d rho).
      Simpl. Intros. Unfold CGSeval. Simpl. Elim (H rho). Intros. Elim (H0 rho). Intros.
      Split. Intro. Elim H5. Intros. Split. Apply H1. Assumption.
      Apply H3. Assumption.
      Intro. Elim H5. Intros. Split. Apply H2. Assumption.
      Apply H4. Assumption.
      Simpl. Intros. Unfold CGSeval. Elim (H rho). Intros. Elim (H0 rho). Intros. Simpl. Split.
      Intro. Elim H5. Intro. Left . Apply H1. Assumption.
      Intro. Right . Apply H3. Assumption.
      Intro. Elim H5. Intro. Left . Apply H2. Assumption.
      Intro. Right . Apply H4. Assumption.
      Simpl. Intros. Unfold CGSeval. Simpl. Elim (H rho). Intros. Elim (H0 rho). Intros. Split.
      Intro. Elim (CGeval_dec c rho). Intro H6. Right . Apply H3. Apply H5. Assumption.
      Intro H6. Left . Elim (CGeval_dec (CG_of_CGS (CGSnot (CGFormSimplify c))) rho). Trivial.
      Intro H7. Elim (H6 (H2 (CGSnot_complete ? ? H7))).
      Intro. Elim H5. Intros. Elim (CGeval_dec (CG_of_CGS (CGFormSimplify c)) rho). Intro H8.
      Elim (CGSnot_correct ? ? H8 H6).
      Intro H8. Elim (H8 (H1 H7)).
      Intros. Apply H4. Assumption. Simpl. Intros. Unfold CGSeval. Simpl. Elim (H rho). Intros.
      Split. Intro. Elim (CGeval_dec (CG_of_CGS (CGSnot (CGFormSimplify c))) rho). Trivial.
      Intro H3. Elim (H2 (H1 (CGSnot_complete ? ? H3))).
      Unfold not. Intros. Elim (CGSnot_correct ? ? (H0 H3) H2).
    Qed.

(*s Formula are solved by looking at their simplified form *)

Definition CG_solve := [f:CGForm] (CGS_solve false (CGFormSimplify f)).

Theorem CG_solve_correct : (f:CGForm) (CG_solve f)=true -> {rho:ad->D | (CGeval rho f)}.
    Proof.
      Intros. Elim (CGS_solve_correct ? ? H). Intros rho H0. Split with rho.
      Apply (proj2 ? ? (CGFormSimplify_correct f rho)). Assumption.
    Qed.

Theorem CG_solve_correct_anchored : (anchor:ad) (anchor_value:D)
      	(f:CGForm) (CG_solve f)=true ->
          {rho:ad->D | (CGeval rho f) /\ (rho anchor)=anchor_value}.
    Proof.
      Intros. Elim (CGS_solve_correct_anchored anchor anchor_value ? ? H). Intros rho H0.
      Split with rho. Elim H0. Intros. Split. Apply (proj2 ? ? (CGFormSimplify_correct f rho)).
      Assumption.
      Assumption.
    Qed.

Theorem CG_solve_complete : (f:CGForm) (rho:ad->D)
        (CGeval rho f) -> (CG_solve f)=true.
    Proof.
      Intros. Unfold CG_solve. Apply (CGS_solve_complete false) with rho:=rho.
      Apply (proj1 ? ? (CGFormSimplify_correct f rho)). Assumption.
    Qed.

(*s A formula is proved when its negation cannot be satisfied *)

Definition CG_prove := [f:CGForm] (negb (CG_solve (CGnot f))).

Theorem CG_prove_correct : (f:CGForm) (CG_prove f)=true -> (rho:ad->D) (CGeval rho f).
    Proof.
      Unfold CG_prove CG_solve. Simpl. Intros. Apply (proj2 ? ? (CGFormSimplify_correct f rho)).
      Apply CGSnot_complete. Unfold not. Intro. Rewrite (CGS_solve_complete false ? ? H0) in H.
      Discriminate H.
    Qed.

Theorem CG_prove_complete : (f:CGForm) ((rho:ad->D) (CGeval rho f)) -> (CG_prove f)=true.
    Proof.
      Unfold CG_prove CG_solve. Simpl. Intros.
      Elim (sumbool_of_bool (CGS_solve false (CGSnot (CGFormSimplify f)))). Intro H0.
      Elim (CGS_solve_correct false ? H0). Intros rho H1.
      Elim (CGSnot_correct ? ? (proj1 ? ? (CGFormSimplify_correct ? ?) (H rho)) H1).
      Intro H0. Rewrite H0. Reflexivity.
    Qed.

Theorem CG_prove_complete_anchored : (f:CGForm) (anchor:ad) (anchor_value:D)
        ((rho:ad->D) (rho anchor)=anchor_value -> (CGeval rho f)) -> (CG_prove f)=true.
    Proof.
      Unfold CG_prove CG_solve. Simpl. Intros.
      Elim (sumbool_of_bool (CGS_solve false (CGSnot (CGFormSimplify f)))). Intro H0.
      Elim (CGS_solve_correct_anchored anchor anchor_value false ? H0). Intros rho H1.
      Elim H1. Intros.
      Elim (CGSnot_correct ? ? (proj1 ? ? (CGFormSimplify_correct f rho) (H rho H3)) H2).
      Intro H0. Rewrite H0. Reflexivity.
    Qed.

  End CGWithOne.

End ConstraintGraphs.
