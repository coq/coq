(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Definition of finite sets as trees indexed by adresses *)

Require Bool.
Require Sumbool.
Require ZArith.
Require Addr.
Require Adist.
Require Addec.


Section MapDefs.

(** We define maps from ad to A. *)
  Variable A : Set.  

  Inductive Map : Set :=
      M0 : Map
    | M1 : ad -> A -> Map
    | M2 : Map -> Map -> Map.

  Inductive option : Set :=
      NONE : option
    | SOME : A -> option.

  Lemma option_sum : (o:option) {y:A | o=(SOME y)}+{o=NONE}.
  Proof.
    Induction o. Right . Reflexivity.
    Left . Split with a. Reflexivity.
  Qed.

  (** The semantics of maps is given by the function [MapGet].
      The semantics of a map [m] is a partial, finite function from
      [ad] to [A]: *)

  Fixpoint MapGet [m:Map] : ad -> option :=
    Cases m of
        M0 => [a:ad] NONE
      | (M1 x y) => [a:ad]
          if (ad_eq x a)
	     then (SOME y)
	  else NONE
      | (M2 m1 m2) => [a:ad]
          Cases a of
	      ad_z => (MapGet m1 ad_z)
	    | (ad_x xH) => (MapGet m2 ad_z)
	    | (ad_x (xO p)) => (MapGet m1 (ad_x p))
	    | (ad_x (xI p)) => (MapGet m2 (ad_x p))
	  end
    end.

  Definition newMap := M0.

  Definition MapSingleton := M1.

  Definition eqm := [g,g':ad->option] (a:ad) (g a)=(g' a).

  Lemma newMap_semantics : (eqm (MapGet newMap) [a:ad] NONE).
  Proof.
    Simpl. Unfold eqm. Trivial.
  Qed.

  Lemma MapSingleton_semantics : (a:ad) (y:A)
      (eqm (MapGet (MapSingleton a y)) [a':ad] if (ad_eq a a') then (SOME y) else NONE).
  Proof.
    Simpl. Unfold eqm. Trivial.
  Qed.

  Lemma M1_semantics_1 : (a:ad) (y:A) (MapGet (M1 a y) a)=(SOME y).
  Proof.
    Unfold MapGet. Intros. Rewrite (ad_eq_correct a). Reflexivity.
  Qed.

  Lemma M1_semantics_2 :
      (a,a':ad) (y:A) (ad_eq a a')=false -> (MapGet (M1 a y) a')=NONE.
  Proof.
    Intros. Simpl. Rewrite H. Reflexivity.
  Qed.

  Lemma Map2_semantics_1 :
      (m,m':Map) (eqm (MapGet m) [a:ad] (MapGet (M2 m m') (ad_double a))).
  Proof.
    Unfold eqm. Induction a; Trivial.
  Qed.

  Lemma Map2_semantics_1_eq : (m,m':Map) (f:ad->option) (eqm (MapGet (M2 m m')) f)
      -> (eqm (MapGet m) [a:ad] (f (ad_double a))).
  Proof.
    Unfold eqm.
    Intros.
    Rewrite <- (H (ad_double a)).
    Exact (Map2_semantics_1 m m' a).
  Qed.

  Lemma Map2_semantics_2 :
      (m,m':Map) (eqm (MapGet m') [a:ad] (MapGet (M2 m m') (ad_double_plus_un a))).
  Proof.
    Unfold eqm. Induction a; Trivial.
  Qed.

  Lemma Map2_semantics_2_eq : (m,m':Map) (f:ad->option) (eqm (MapGet (M2 m m')) f)
      -> (eqm (MapGet m') [a:ad] (f (ad_double_plus_un a))).
  Proof.
    Unfold eqm.
    Intros.
    Rewrite <- (H (ad_double_plus_un a)).
    Exact (Map2_semantics_2 m m' a).
  Qed.

  Lemma MapGet_M2_bit_0_0 : (a:ad) (ad_bit_0 a)=false
      -> (m,m':Map) (MapGet (M2 m m') a)=(MapGet m (ad_div_2 a)).
  Proof.
    Induction a; Trivial. Induction p. Intros. Discriminate H0.
    Trivial.
    Intros. Discriminate H.
  Qed.

  Lemma MapGet_M2_bit_0_1 : (a:ad) (ad_bit_0 a)=true
      -> (m,m':Map) (MapGet (M2 m m') a)=(MapGet m' (ad_div_2 a)).
  Proof.
    Induction a. Intros. Discriminate H.
    Induction p. Trivial.
    Intros. Discriminate H0.
    Trivial.
  Qed.

  Lemma MapGet_M2_bit_0_if : (m,m':Map) (a:ad) (MapGet (M2 m m') a)=
      (if (ad_bit_0 a) then (MapGet m' (ad_div_2 a)) else (MapGet m (ad_div_2 a))).
  Proof.
    Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H. Rewrite H.
    Apply MapGet_M2_bit_0_1; Assumption.
    Intro H. Rewrite H. Apply MapGet_M2_bit_0_0; Assumption.
  Qed.

  Lemma MapGet_M2_bit_0 : (m,m',m'':Map)
      (a:ad) (if (ad_bit_0 a) then (MapGet (M2 m' m) a) else (MapGet (M2 m m'') a))=
             (MapGet m (ad_div_2 a)).
  Proof.
    Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H. Rewrite H.
    Apply MapGet_M2_bit_0_1; Assumption.
    Intro H. Rewrite H. Apply MapGet_M2_bit_0_0; Assumption.
  Qed.

  Lemma Map2_semantics_3 : (m,m':Map) (eqm (MapGet (M2 m m'))
      [a:ad] Cases (ad_bit_0 a) of
                 false => (MapGet m (ad_div_2 a))
	       | true => (MapGet m' (ad_div_2 a))
	     end).
  Proof.
    Unfold eqm.
    Induction a; Trivial.
    Induction p; Trivial.
  Qed.

  Lemma Map2_semantics_3_eq : (m,m':Map) (f,f':ad->option)
      (eqm (MapGet m) f) -> (eqm (MapGet m') f') -> (eqm (MapGet (M2 m m'))
      [a:ad] Cases (ad_bit_0 a) of
                 false => (f (ad_div_2 a))
	       | true => (f' (ad_div_2 a))
	     end).
  Proof.
    Unfold eqm.
    Intros.
    Rewrite <- (H (ad_div_2 a)).
    Rewrite <- (H0 (ad_div_2 a)).
    Exact (Map2_semantics_3 m m' a).
  Qed.

  Fixpoint MapPut1 [a:ad; y:A; a':ad; y':A; p:positive] : Map :=
    Cases p of
        (xO p') => let m = (MapPut1 (ad_div_2 a) y (ad_div_2 a') y' p') in
      	           Cases (ad_bit_0 a) of
      	               false => (M2 m M0)
		     | true => (M2 M0 m)
		   end
      | _ => Cases (ad_bit_0 a) of
                 false => (M2 (M1 (ad_div_2 a) y) (M1 (ad_div_2 a') y'))
	       | true => (M2 (M1 (ad_div_2 a') y') (M1 (ad_div_2 a) y))
	     end
    end.

  Lemma MapGet_if_commute : (b:bool) (m,m':Map) (a:ad)
      (MapGet (if b then m else m') a)=(if b then (MapGet m a) else (MapGet m' a)).
  Proof.
    Intros. Case b; Trivial.
  Qed.

  (*i
  Lemma MapGet_M2_bit_0_1' : (m,m',m'',m''':Map)
      (a:ad) (MapGet (if (ad_bit_0 a) then (M2 m m') else (M2 m'' m''')) a)=
             (MapGet (if (ad_bit_0 a) then m' else m'') (ad_div_2 a)).
  Proof.
    Intros. Rewrite (MapGet_if_commute (ad_bit_0 a)). Rewrite (MapGet_if_commute (ad_bit_0 a)).
    Cut (ad_bit_0 a)=false\/(ad_bit_0 a)=true. Intros. Elim H. Intros. Rewrite H0.
    Apply MapGet_M2_bit_0_0. Assumption.
    Intros. Rewrite H0. Apply MapGet_M2_bit_0_1. Assumption.
    Case (ad_bit_0 a); Auto.
  Qed.
  i*)

  Lemma MapGet_if_same : (m:Map) (b:bool) (a:ad) 
      (MapGet (if b then m else m) a)=(MapGet m a).
  Proof.
    Induction b;Trivial.
  Qed.

  Lemma MapGet_M2_bit_0_2 : (m,m',m'':Map)
      (a:ad) (MapGet (if (ad_bit_0 a) then (M2 m m') else (M2 m' m'')) a)=
             (MapGet m' (ad_div_2 a)).
  Proof.
    Intros. Rewrite MapGet_if_commute. Apply MapGet_M2_bit_0.
  Qed.

  Lemma MapPut1_semantics_1 : (p:positive) (a,a':ad) (y,y':A)
      (ad_xor a a')=(ad_x p)
      	-> (MapGet (MapPut1 a y a' y' p) a)=(SOME y).
  Proof.
    Induction p. Intros. Unfold MapPut1. Rewrite MapGet_M2_bit_0_2. Apply M1_semantics_1.
    Intros. Simpl. Rewrite MapGet_M2_bit_0_2. Apply H. Rewrite <- ad_xor_div_2. Rewrite H0.
    Reflexivity.
    Intros. Unfold MapPut1. Rewrite MapGet_M2_bit_0_2. Apply M1_semantics_1.
  Qed.

  Lemma MapPut1_semantics_2 : (p:positive) (a,a':ad) (y,y':A)
      (ad_xor a a')=(ad_x p)
      	-> (MapGet (MapPut1 a y a' y' p) a')=(SOME y').
  Proof.
    Induction p. Intros. Unfold MapPut1. Rewrite (ad_neg_bit_0_2 a a' p0 H0).
    Rewrite if_negb. Rewrite MapGet_M2_bit_0_2. Apply M1_semantics_1.
    Intros. Simpl. Rewrite (ad_same_bit_0 a a' p0 H0). Rewrite MapGet_M2_bit_0_2.
    Apply H. Rewrite <- ad_xor_div_2. Rewrite H0. Reflexivity.
    Intros. Unfold MapPut1. Rewrite (ad_neg_bit_0_1 a a' H). Rewrite if_negb.
    Rewrite MapGet_M2_bit_0_2. Apply M1_semantics_1.
  Qed.

  Lemma MapGet_M2_both_NONE : (m,m':Map) (a:ad)
      (MapGet m (ad_div_2 a))=NONE -> (MapGet m' (ad_div_2 a))=NONE -> 
        (MapGet (M2 m m') a)=NONE.
  Proof.
    Intros. Rewrite (Map2_semantics_3 m m' a). 
    Case (ad_bit_0 a); Assumption.
  Qed.
 
  Lemma MapPut1_semantics_3 : (p:positive) (a,a',a0:ad) (y,y':A)
      	(ad_xor a a')=(ad_x p) -> (ad_eq a a0)=false -> (ad_eq a' a0)=false ->
	  (MapGet (MapPut1 a y a' y' p) a0)=NONE.
  Proof.
    Induction p. Intros. Unfold MapPut1. Elim (ad_neq a a0 H1). Intro. Rewrite H3. Rewrite if_negb.
    Rewrite MapGet_M2_bit_0_2. Apply M1_semantics_2. Apply ad_div_bit_neq. Assumption.
    Rewrite (ad_neg_bit_0_2 a a' p0 H0) in H3. Rewrite (negb_intro (ad_bit_0 a')).
    Rewrite (negb_intro (ad_bit_0 a0)). Rewrite H3. Reflexivity.
    Intro. Elim (ad_neq a' a0 H2). Intro. Rewrite (ad_neg_bit_0_2 a a' p0 H0). Rewrite H4.
    Rewrite (negb_elim (ad_bit_0 a0)). Rewrite MapGet_M2_bit_0_2.
    Apply M1_semantics_2; Assumption.
    Intro; Case (ad_bit_0 a); Apply MapGet_M2_both_NONE; 
	Apply M1_semantics_2; Assumption.
    Intros. Simpl. Elim (ad_neq a a0 H1). Intro. Rewrite H3. Rewrite if_negb.
    Rewrite MapGet_M2_bit_0_2. Reflexivity.
    Intro. Elim (ad_neq a' a0 H2). Intro. Rewrite (ad_same_bit_0 a a' p0 H0). Rewrite H4.
    Rewrite if_negb. Rewrite MapGet_M2_bit_0_2. Reflexivity.
    Intro. Cut (ad_xor (ad_div_2 a) (ad_div_2 a'))=(ad_x p0). Intro.
    Case (ad_bit_0 a); Apply MapGet_M2_both_NONE; Trivial; 
	Apply H; Assumption.
    Rewrite <- ad_xor_div_2. Rewrite H0. Reflexivity.
    Intros. Simpl. Elim (ad_neq a a0 H0). Intro. Rewrite H2. Rewrite if_negb.
    Rewrite MapGet_M2_bit_0_2. Apply M1_semantics_2. Apply ad_div_bit_neq. Assumption.
    Rewrite (ad_neg_bit_0_1 a a' H) in H2. Rewrite (negb_intro (ad_bit_0 a')).
    Rewrite (negb_intro (ad_bit_0 a0)). Rewrite H2. Reflexivity.
    Intro. Elim (ad_neq a' a0 H1). Intro. Rewrite (ad_neg_bit_0_1 a a' H). Rewrite H3.
    Rewrite (negb_elim (ad_bit_0 a0)). Rewrite MapGet_M2_bit_0_2.
    Apply M1_semantics_2; Assumption.
    Intro. Case (ad_bit_0 a); Apply MapGet_M2_both_NONE; Apply M1_semantics_2; Assumption.
  Qed.

  Lemma MapPut1_semantics : (p:positive) (a,a':ad) (y,y':A)
      (ad_xor a a')=(ad_x p)
        -> (eqm (MapGet (MapPut1 a y a' y' p))
	        [a0:ad] if (ad_eq a a0) then (SOME y)
		        else if (ad_eq a' a0) then (SOME y') else NONE).
  Proof.
    Unfold eqm. Intros. Elim (sumbool_of_bool (ad_eq a a0)). Intro H0. Rewrite H0.
    Rewrite <- (ad_eq_complete ? ? H0). Exact (MapPut1_semantics_1 p a a' y y' H).
    Intro H0. Rewrite H0. Elim (sumbool_of_bool (ad_eq a' a0)). Intro H1.
    Rewrite <- (ad_eq_complete ? ? H1). Rewrite (ad_eq_correct a').
    Exact (MapPut1_semantics_2 p a a' y y' H).
    Intro H1. Rewrite H1. Exact (MapPut1_semantics_3 p a a' a0 y y' H H0 H1).
  Qed.

  Lemma MapPut1_semantics' : (p:positive) (a,a':ad) (y,y':A)
      (ad_xor a a')=(ad_x p)
        -> (eqm (MapGet (MapPut1 a y a' y' p))
	        [a0:ad] if (ad_eq a' a0) then (SOME y')
		        else if (ad_eq a a0) then (SOME y) else NONE).
  Proof.
    Unfold eqm. Intros. Rewrite (MapPut1_semantics p a a' y y' H a0).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H0. Rewrite H0.
    Rewrite <- (ad_eq_complete a a0 H0). Rewrite (ad_eq_comm a' a).
    Rewrite (ad_xor_eq_false a a' p H). Reflexivity.
    Intro H0. Rewrite H0. Reflexivity.
  Qed.

  Fixpoint MapPut [m:Map] : ad -> A -> Map :=
    Cases m of
        M0 => M1
      | (M1 a y) => [a':ad; y':A]
          Cases (ad_xor a a') of
	      ad_z => (M1 a' y')
	    | (ad_x p) => (MapPut1 a y a' y' p)
          end
      | (M2 m1 m2) => [a:ad; y:A]
          Cases a of
	      ad_z => (M2 (MapPut m1 ad_z y) m2)
	    | (ad_x xH) => (M2 m1 (MapPut m2 ad_z y))
	    | (ad_x (xO p)) => (M2 (MapPut m1 (ad_x p) y) m2)
	    | (ad_x (xI p)) => (M2 m1 (MapPut m2 (ad_x p) y))
	  end
    end.

  Lemma MapPut_semantics_1 : (a:ad) (y:A) (a0:ad)
      (MapGet (MapPut M0 a y) a0)=(MapGet (M1 a y) a0).
  Proof.
    Trivial.
  Qed.

  Lemma MapPut_semantics_2_1 : (a:ad) (y,y':A) (a0:ad)
      (MapGet (MapPut (M1 a y) a y') a0)=(if (ad_eq a a0) then (SOME y') else NONE).
  Proof.
    Simpl. Intros. Rewrite (ad_xor_nilpotent a). Trivial.
  Qed.

  Lemma MapPut_semantics_2_2 : (a,a':ad) (y,y':A) (a0:ad) (a'':ad) (ad_xor a a')=a'' ->
      (MapGet (MapPut (M1 a y) a' y') a0)=
      (if (ad_eq a' a0) then (SOME y') else
       if (ad_eq a a0) then (SOME y) else NONE).
  Proof.
    Induction a''. Intro. Rewrite (ad_xor_eq ? ? H). Rewrite MapPut_semantics_2_1.
    Case (ad_eq a' a0); Trivial.
    Intros. Simpl. Rewrite H. Rewrite (MapPut1_semantics p a a' y y' H a0).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H0. Rewrite H0. Rewrite <- (ad_eq_complete ? ? H0).
    Rewrite (ad_eq_comm a' a). Rewrite (ad_xor_eq_false ? ? ? H). Reflexivity.
    Intro H0. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapPut_semantics_2 : (a,a':ad) (y,y':A) (a0:ad)
      (MapGet (MapPut (M1 a y) a' y') a0)=
      (if (ad_eq a' a0) then (SOME y') else
       if (ad_eq a a0) then (SOME y) else NONE).
  Proof.
    Intros. Apply MapPut_semantics_2_2 with a'':=(ad_xor a a'); Trivial.
  Qed.

  Lemma MapPut_semantics_3_1 : (m,m':Map) (a:ad) (y:A)
      (MapPut (M2 m m') a y)=(if (ad_bit_0 a) then (M2 m (MapPut m' (ad_div_2 a) y))
                                              else (M2 (MapPut m (ad_div_2 a) y) m')).
  Proof.
    Induction a. Trivial.
    Induction p; Trivial.
  Qed.

  Lemma MapPut_semantics : (m:Map) (a:ad) (y:A)
      (eqm (MapGet (MapPut m a y)) [a':ad] if (ad_eq a a') then (SOME y) else (MapGet m a')).
  Proof.
    Unfold eqm. Induction m. Exact MapPut_semantics_1.
    Intros. Unfold 2 MapGet. Apply MapPut_semantics_2; Assumption.
    Intros. Rewrite MapPut_semantics_3_1. Rewrite (MapGet_M2_bit_0_if m0 m1 a0).
    Elim (sumbool_of_bool (ad_bit_0 a)). Intro H1. Rewrite H1. Rewrite MapGet_M2_bit_0_if.
    Elim (sumbool_of_bool (ad_bit_0 a0)). Intro H2. Rewrite H2.
    Rewrite (H0 (ad_div_2 a) y (ad_div_2 a0)). Elim (sumbool_of_bool (ad_eq a a0)).
    Intro H3. Rewrite H3. Rewrite (ad_div_eq ? ? H3). Reflexivity.
    Intro H3. Rewrite H3. Rewrite <- H2 in H1. Rewrite (ad_div_bit_neq ? ? H3 H1). Reflexivity.
    Intro H2. Rewrite H2. Rewrite (ad_eq_comm a a0). Rewrite (ad_bit_0_neq a0 a H2 H1).
    Reflexivity.
    Intro H1. Rewrite H1. Rewrite MapGet_M2_bit_0_if. Elim (sumbool_of_bool (ad_bit_0 a0)).
    Intro H2. Rewrite H2. Rewrite (ad_bit_0_neq a a0 H1 H2). Reflexivity.
    Intro H2. Rewrite H2. Rewrite (H (ad_div_2 a) y (ad_div_2 a0)).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H3. Rewrite H3.
    Rewrite (ad_div_eq a a0 H3). Reflexivity.
    Intro H3. Rewrite H3. Rewrite <- H2 in H1. Rewrite (ad_div_bit_neq a a0 H3 H1). Reflexivity.
  Qed.

  Fixpoint MapPut_behind [m:Map] : ad -> A -> Map :=
    Cases m of
        M0 => M1
      | (M1 a y) => [a':ad; y':A]
          Cases (ad_xor a a') of
	      ad_z => m
	    | (ad_x p) => (MapPut1 a y a' y' p)
          end
      | (M2 m1 m2) => [a:ad; y:A]
          Cases a of
	      ad_z => (M2 (MapPut_behind m1 ad_z y) m2)
	    | (ad_x xH) => (M2 m1 (MapPut_behind m2 ad_z y))
	    | (ad_x (xO p)) => (M2 (MapPut_behind m1 (ad_x p) y) m2)
	    | (ad_x (xI p)) => (M2 m1 (MapPut_behind m2 (ad_x p) y))
	  end
    end.

  Lemma MapPut_behind_semantics_3_1 : (m,m':Map) (a:ad) (y:A)
      (MapPut_behind (M2 m m') a y)=
      (if (ad_bit_0 a) then (M2 m (MapPut_behind m' (ad_div_2 a) y))
                       else (M2 (MapPut_behind m (ad_div_2 a) y) m')).
  Proof.
    Induction a. Trivial.
    Induction p; Trivial.
  Qed.

  Lemma MapPut_behind_as_before_1 : (a,a',a0:ad) (ad_eq a' a0)=false ->
      (y,y':A) (MapGet (MapPut (M1 a y) a' y') a0)
               =(MapGet (MapPut_behind (M1 a y) a' y') a0).
  Proof.
    Intros a a' a0. Simpl. Intros H y y'. Elim (ad_sum (ad_xor a a')). Intro H0. Elim H0.
    Intros p H1. Rewrite H1. Reflexivity.
    Intro H0. Rewrite H0. Rewrite (ad_xor_eq ? ? H0). Rewrite (M1_semantics_2 a' a0 y H).
    Exact (M1_semantics_2 a' a0 y' H).
  Qed.

  Lemma MapPut_behind_as_before : (m:Map) (a:ad) (y:A)
      (a0:ad) (ad_eq a a0)=false ->
         (MapGet (MapPut m a y) a0)=(MapGet (MapPut_behind m a y) a0).
  Proof.
    Induction m. Trivial.
    Intros a y a' y' a0 H. Exact (MapPut_behind_as_before_1 a a' a0 H y y').
    Intros. Rewrite MapPut_semantics_3_1. Rewrite MapPut_behind_semantics_3_1.
    Elim (sumbool_of_bool (ad_bit_0 a)). Intro H2. Rewrite H2. Rewrite MapGet_M2_bit_0_if.
    Rewrite MapGet_M2_bit_0_if. Elim (sumbool_of_bool (ad_bit_0 a0)). Intro H3.
    Rewrite H3. Apply H0. Rewrite <- H3 in H2. Exact (ad_div_bit_neq a a0 H1 H2).
    Intro H3. Rewrite H3. Reflexivity.
    Intro H2. Rewrite H2. Rewrite MapGet_M2_bit_0_if. Rewrite MapGet_M2_bit_0_if.
    Elim (sumbool_of_bool (ad_bit_0 a0)). Intro H3. Rewrite H3. Reflexivity.
    Intro H3. Rewrite H3. Apply H. Rewrite <- H3 in H2. Exact (ad_div_bit_neq a a0 H1 H2).
  Qed.

  Lemma MapPut_behind_new : (m:Map) (a:ad) (y:A)
      (MapGet (MapPut_behind m a y) a)=(Cases (MapGet m a) of
                                            (SOME y') => (SOME y')
					  | _ => (SOME y)
				        end).
  Proof.
    Induction m. Simpl. Intros. Rewrite (ad_eq_correct a). Reflexivity.
    Intros. Elim (ad_sum (ad_xor a a1)). Intro H. Elim H. Intros p H0. Simpl.
    Rewrite H0. Rewrite (ad_xor_eq_false a a1 p). Exact (MapPut1_semantics_2 p a a1 a0 y H0).
    Assumption.
    Intro H. Simpl. Rewrite H. Rewrite <- (ad_xor_eq ? ? H). Rewrite (ad_eq_correct a).
    Exact (M1_semantics_1 a a0).
    Intros. Rewrite MapPut_behind_semantics_3_1. Rewrite (MapGet_M2_bit_0_if m0 m1 a).
    Elim (sumbool_of_bool (ad_bit_0 a)). Intro H1. Rewrite H1. Rewrite (MapGet_M2_bit_0_1 a H1).
    Exact (H0 (ad_div_2 a) y).
    Intro H1. Rewrite H1. Rewrite (MapGet_M2_bit_0_0 a H1). Exact (H (ad_div_2 a) y).
  Qed.

  Lemma MapPut_behind_semantics : (m:Map) (a:ad) (y:A)
      (eqm (MapGet (MapPut_behind m a y))
           [a':ad] Cases (MapGet m a') of
                       (SOME y') => (SOME y')
		     | _ => if (ad_eq a a') then (SOME y) else NONE
		   end).
  Proof.
    Unfold eqm. Intros. Elim (sumbool_of_bool (ad_eq a a0)). Intro H. Rewrite H.
    Rewrite (ad_eq_complete ? ? H). Apply MapPut_behind_new.
    Intro H. Rewrite H. Rewrite <- (MapPut_behind_as_before m a y a0 H).
    Rewrite (MapPut_semantics m a y a0). Rewrite H. Case (MapGet m a0); Trivial.
  Qed.

  Definition makeM2 := [m,m':Map] Cases m m' of
                                      M0 M0 => M0
				    | M0 (M1 a y) => (M1 (ad_double_plus_un a) y)
				    | (M1 a y) M0 => (M1 (ad_double a) y)
				    | _ _ => (M2 m m')
				  end.

  Lemma makeM2_M2 : (m,m':Map) (eqm (MapGet (makeM2 m m')) (MapGet (M2 m m'))).
  Proof.
    Unfold eqm. Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H.
    Rewrite (MapGet_M2_bit_0_1 a H m m'). Case m'. Case m. Reflexivity.
    Intros a0 y. Simpl. Rewrite (ad_bit_0_1_not_double a H a0). Reflexivity.
    Intros m1 m2. Unfold makeM2. Rewrite MapGet_M2_bit_0_1. Reflexivity.
    Assumption.
    Case m. Intros a0 y. Simpl. Elim (sumbool_of_bool (ad_eq a0 (ad_div_2 a))).
    Intro H0. Rewrite H0. Rewrite (ad_eq_complete ? ? H0). Rewrite (ad_div_2_double_plus_un a H).
    Rewrite (ad_eq_correct a). Reflexivity.
    Intro H0. Rewrite H0. Rewrite (ad_eq_comm a0 (ad_div_2 a)) in H0.
    Rewrite (ad_not_div_2_not_double_plus_un a a0 H0). Reflexivity.
    Intros a0 y0 a1 y1. Unfold makeM2. Rewrite MapGet_M2_bit_0_1. Reflexivity.
    Assumption.
    Intros m1 m2 a0 y. Unfold makeM2. Rewrite MapGet_M2_bit_0_1. Reflexivity.
    Assumption.
    Intros m1 m2. Unfold makeM2.
    Cut (MapGet (M2 m (M2 m1 m2)) a)=(MapGet (M2 m1 m2) (ad_div_2 a)). 
    Case m; Trivial.
    Exact (MapGet_M2_bit_0_1 a H m (M2 m1 m2)).
    Intro H. Rewrite (MapGet_M2_bit_0_0 a H m m'). Case m. Case m'. Reflexivity.
    Intros a0 y. Simpl. Rewrite (ad_bit_0_0_not_double_plus_un a H a0). Reflexivity.
    Intros m1 m2. Unfold makeM2. Rewrite MapGet_M2_bit_0_0. Reflexivity.
    Assumption.
    Case m'. Intros a0 y. Simpl. Elim (sumbool_of_bool (ad_eq a0 (ad_div_2 a))). Intro H0.
    Rewrite H0. Rewrite (ad_eq_complete ? ? H0). Rewrite (ad_div_2_double a H).
    Rewrite (ad_eq_correct a). Reflexivity.
    Intro H0. Rewrite H0. Rewrite (ad_eq_comm (ad_double a0) a).
    Rewrite (ad_eq_comm a0 (ad_div_2 a)) in H0. Rewrite (ad_not_div_2_not_double a a0 H0).
    Reflexivity.
    Intros a0 y0 a1 y1. Unfold makeM2. Rewrite MapGet_M2_bit_0_0. Reflexivity.
    Assumption.
    Intros m1 m2 a0 y. Unfold makeM2. Rewrite MapGet_M2_bit_0_0. Reflexivity.
    Assumption.
    Intros m1 m2. Unfold makeM2. Exact (MapGet_M2_bit_0_0 a H (M2 m1 m2) m').
  Qed.

  Fixpoint MapRemove [m:Map] : ad -> Map :=
    Cases m of
        M0 => [_:ad] M0
      | (M1 a y) => [a':ad]
          Cases (ad_eq a a') of
	      true => M0
	    | false => m
          end
      | (M2 m1 m2) => [a:ad]
          if (ad_bit_0 a)
	  then (makeM2 m1 (MapRemove m2 (ad_div_2 a)))
	  else (makeM2 (MapRemove m1 (ad_div_2 a)) m2)
    end.

  Lemma MapRemove_semantics : (m:Map) (a:ad)
      (eqm (MapGet (MapRemove m a)) [a':ad] if (ad_eq a a') then NONE else (MapGet m a')).
  Proof.
    Unfold eqm. Induction m. Simpl. Intros. Case (ad_eq a a0); Trivial.
    Intros. Simpl. Elim (sumbool_of_bool (ad_eq a1 a2)). Intro H. Rewrite H.
    Elim (sumbool_of_bool (ad_eq a a1)). Intro H0. Rewrite H0. Reflexivity.
    Intro H0. Rewrite H0. Rewrite (ad_eq_complete ? ? H) in H0. Exact (M1_semantics_2 a a2 a0 H0).
    Intro H. Elim (sumbool_of_bool (ad_eq a a1)). Intro H0. Rewrite H0. Rewrite H.
    Rewrite <- (ad_eq_complete ? ? H0) in H. Rewrite H. Reflexivity.
    Intro H0. Rewrite H0. Rewrite H. Reflexivity.
    Intros. Change (MapGet (if (ad_bit_0 a)
                            then (makeM2 m0 (MapRemove m1 (ad_div_2 a)))
                            else (makeM2 (MapRemove m0 (ad_div_2 a)) m1))
			   a0)
                   =(if (ad_eq a a0) then NONE else (MapGet (M2 m0 m1) a0)).
    Elim (sumbool_of_bool (ad_bit_0 a)). Intro H1. Rewrite H1.
    Rewrite (makeM2_M2 m0 (MapRemove m1 (ad_div_2 a)) a0). Elim (sumbool_of_bool (ad_bit_0 a0)).
    Intro H2. Rewrite MapGet_M2_bit_0_1. Rewrite (H0 (ad_div_2 a) (ad_div_2 a0)).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H3. Rewrite H3. Rewrite (ad_div_eq ? ? H3).
    Reflexivity.
    Intro H3. Rewrite H3. Rewrite <- H2 in H1. Rewrite (ad_div_bit_neq ? ? H3 H1).
    Rewrite (MapGet_M2_bit_0_1 a0 H2 m0 m1). Reflexivity.
    Assumption.
    Intro H2. Rewrite (MapGet_M2_bit_0_0 a0 H2 m0 (MapRemove m1 (ad_div_2 a))).
    Rewrite (ad_eq_comm a a0). Rewrite (ad_bit_0_neq ? ? H2 H1).
    Rewrite (MapGet_M2_bit_0_0 a0 H2 m0 m1). Reflexivity.
    Intro H1. Rewrite H1. Rewrite (makeM2_M2 (MapRemove m0 (ad_div_2 a)) m1 a0).
    Elim (sumbool_of_bool (ad_bit_0 a0)). Intro H2. Rewrite MapGet_M2_bit_0_1.
    Rewrite (MapGet_M2_bit_0_1 a0 H2 m0 m1). Rewrite (ad_bit_0_neq a a0 H1 H2). Reflexivity.
    Assumption.
    Intro H2. Rewrite MapGet_M2_bit_0_0. Rewrite (H (ad_div_2 a) (ad_div_2 a0)).
    Rewrite (MapGet_M2_bit_0_0 a0 H2 m0 m1). Elim (sumbool_of_bool (ad_eq a a0)). Intro H3.
    Rewrite H3. Rewrite (ad_div_eq ? ? H3). Reflexivity.
    Intro H3. Rewrite H3. Rewrite <- H2 in H1. Rewrite (ad_div_bit_neq ? ? H3 H1). Reflexivity.
    Assumption.
  Qed.

  Fixpoint MapCard [m:Map] : nat :=
    Cases m of
        M0 => O
      | (M1 _ _) => (S O)
      | (M2 m m') => (plus (MapCard m) (MapCard m'))
    end.

  Fixpoint MapMerge [m:Map] : Map -> Map :=
    Cases m of
        M0 => [m':Map] m'
      | (M1 a y) => [m':Map] (MapPut_behind m' a y)
      | (M2 m1 m2) => [m':Map] Cases m' of
      	                           M0 => m
				 | (M1 a' y') => (MapPut m a' y')
				 | (M2 m'1 m'2) => (M2 (MapMerge m1 m'1) 
	                                               (MapMerge m2 m'2))
			       end
    end.

  Lemma MapMerge_semantics : (m,m':Map)
      (eqm (MapGet (MapMerge m m'))
           [a0:ad] Cases (MapGet m' a0) of
	               (SOME y') => (SOME y')
		     | NONE => (MapGet m a0)
                   end).
  Proof.
    Unfold eqm. Induction m. Intros. Simpl. Case (MapGet m' a); Trivial.
    Intros. Simpl. Rewrite (MapPut_behind_semantics m' a a0 a1). Reflexivity.
    Induction m'. Trivial.
    Intros. Unfold MapMerge. Rewrite (MapPut_semantics (M2 m0 m1) a a0 a1).
    Elim (sumbool_of_bool (ad_eq a a1)). Intro H1. Rewrite H1. Rewrite (ad_eq_complete ? ? H1).
    Rewrite (M1_semantics_1 a1 a0). Reflexivity.
    Intro H1. Rewrite H1. Rewrite (M1_semantics_2 a a1 a0 H1). Reflexivity.
    Intros. Cut (MapMerge (M2 m0 m1) (M2 m2 m3))=(M2 (MapMerge m0 m2) (MapMerge m1 m3)).
    Intro. Rewrite H3. Rewrite MapGet_M2_bit_0_if. Rewrite (H0 m3 (ad_div_2 a)).
    Rewrite (H m2 (ad_div_2 a)). Rewrite (MapGet_M2_bit_0_if m2 m3 a).
    Rewrite (MapGet_M2_bit_0_if m0 m1 a). Case (ad_bit_0 a); Trivial.
    Reflexivity.
  Qed.

  (** [MapInter], [MapRngRestrTo], [MapRngRestrBy], [MapInverse] 
      not implemented: need a decidable equality on [A]. *)

  Fixpoint MapDelta [m:Map] : Map -> Map :=
    Cases m of
        M0 => [m':Map] m'
      | (M1 a y) => [m':Map] Cases (MapGet m' a) of
                                 NONE => (MapPut m' a y)
			       | _ => (MapRemove m' a)
			     end
      | (M2 m1 m2) => [m':Map] Cases m' of
                                   M0 => m
				 | (M1 a' y') => Cases (MapGet m a') of
				                     NONE => (MapPut m a' y')
						   | _ => (MapRemove m a')
						 end
				 | (M2 m'1 m'2) => (makeM2 (MapDelta m1 m'1)
				                           (MapDelta m2 m'2))
			       end
    end.

  Lemma MapDelta_semantics_comm : (m,m':Map)
      (eqm (MapGet (MapDelta m m')) (MapGet (MapDelta m' m))).
  Proof.
    Unfold eqm. Induction m. Induction m'; Reflexivity.
    Induction m'. Reflexivity.
    Unfold MapDelta. Intros. Elim (sumbool_of_bool (ad_eq a a1)). Intro H.
    Rewrite <- (ad_eq_complete ? ? H). Rewrite (M1_semantics_1 a a2).
    Rewrite (M1_semantics_1 a a0). Simpl. Rewrite (ad_eq_correct a). Reflexivity.
    Intro H. Rewrite (M1_semantics_2 a a1 a0 H). Rewrite (ad_eq_comm a a1) in H.
    Rewrite (M1_semantics_2 a1 a a2 H). Rewrite (MapPut_semantics (M1 a a0) a1 a2 a3).
    Rewrite (MapPut_semantics (M1 a1 a2) a a0 a3). Elim (sumbool_of_bool (ad_eq a a3)).
    Intro H0. Rewrite H0. Rewrite (ad_eq_complete ? ? H0) in H. Rewrite H.
    Rewrite (ad_eq_complete ? ? H0). Rewrite (M1_semantics_1 a3 a0). Reflexivity.
    Intro H0. Rewrite H0. Rewrite (M1_semantics_2 a a3 a0 H0).
    Elim (sumbool_of_bool (ad_eq a1 a3)). Intro H1. Rewrite H1.
    Rewrite (ad_eq_complete ? ? H1). Exact (M1_semantics_1 a3 a2).
    Intro H1. Rewrite H1. Exact (M1_semantics_2 a1 a3 a2 H1).
    Intros. Reflexivity.
    Induction m'. Reflexivity.
    Reflexivity.
    Intros. Simpl. Rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    Rewrite (makeM2_M2 (MapDelta m2 m0) (MapDelta m3 m1) a).
    Rewrite (MapGet_M2_bit_0_if (MapDelta m0 m2) (MapDelta m1 m3) a).
    Rewrite (MapGet_M2_bit_0_if (MapDelta m2 m0) (MapDelta m3 m1) a).
    Rewrite (H0 m3 (ad_div_2 a)). Rewrite (H m2 (ad_div_2 a)). Reflexivity.
  Qed.

  Lemma MapDelta_semantics_1_1 : (a:ad) (y:A) (m':Map) (a0:ad)
    (MapGet (M1 a y) a0)=NONE -> (MapGet m' a0)=NONE -> 
      (MapGet (MapDelta (M1 a y) m') a0)=NONE.
  Proof.
    Intros. Unfold MapDelta. Elim (sumbool_of_bool (ad_eq a a0)). Intro H1.
    Rewrite (ad_eq_complete ? ? H1) in H. Rewrite (M1_semantics_1 a0 y) in H. Discriminate H.
    Intro H1. Case (MapGet m' a). Rewrite (MapPut_semantics m' a y a0). Rewrite H1. Assumption.
    Rewrite (MapRemove_semantics m' a a0). Rewrite H1. Trivial.
  Qed.

  Lemma MapDelta_semantics_1 : (m,m':Map) (a:ad)
    (MapGet m a)=NONE -> (MapGet m' a)=NONE -> 
      (MapGet (MapDelta m m') a)=NONE.
  Proof.
    Induction m. Trivial.
    Exact MapDelta_semantics_1_1.
    Induction m'. Trivial.
    Intros. Rewrite (MapDelta_semantics_comm (M2 m0 m1) (M1 a a0) a1).
    Apply MapDelta_semantics_1_1; Trivial.
    Intros. Simpl. Rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    Rewrite MapGet_M2_bit_0_if. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H5. Rewrite H5.
    Apply H0. Rewrite (MapGet_M2_bit_0_1 a H5 m0 m1) in H3. Exact H3.
    Rewrite (MapGet_M2_bit_0_1 a H5 m2 m3) in H4. Exact H4.
    Intro H5. Rewrite H5. Apply H. Rewrite (MapGet_M2_bit_0_0 a H5 m0 m1) in H3. Exact H3.
    Rewrite (MapGet_M2_bit_0_0 a H5 m2 m3) in H4. Exact H4.
  Qed.

  Lemma MapDelta_semantics_2_1 : (a:ad) (y:A) (m':Map) (a0:ad) (y0:A)
    (MapGet (M1 a y) a0)=NONE -> (MapGet m' a0)=(SOME y0) ->
      (MapGet (MapDelta (M1 a y) m') a0)=(SOME y0).
  Proof.
    Intros. Unfold MapDelta. Elim (sumbool_of_bool (ad_eq a a0)). Intro H1.
    Rewrite (ad_eq_complete ? ? H1) in H. Rewrite (M1_semantics_1 a0 y) in H. Discriminate H.
    Intro H1. Case (MapGet m' a). Rewrite (MapPut_semantics m' a y a0). Rewrite H1. Assumption.
    Rewrite (MapRemove_semantics m' a a0). Rewrite H1. Trivial.
  Qed.

  Lemma MapDelta_semantics_2_2 : (a:ad) (y:A) (m':Map) (a0:ad) (y0:A)
    (MapGet (M1 a y) a0)=(SOME y0) -> (MapGet m' a0)=NONE ->
      (MapGet (MapDelta (M1 a y) m') a0)=(SOME y0).
  Proof.
    Intros. Unfold MapDelta. Elim (sumbool_of_bool (ad_eq a a0)). Intro H1.
    Rewrite (ad_eq_complete ? ? H1) in H. Rewrite (ad_eq_complete ? ? H1).
    Rewrite H0. Rewrite (MapPut_semantics m' a0 y a0). Rewrite (ad_eq_correct a0).
    Rewrite (M1_semantics_1 a0 y) in H. Simple Inversion H. Assumption.
    Intro H1. Rewrite (M1_semantics_2 a a0 y H1) in H. Discriminate H.
  Qed.

  Lemma MapDelta_semantics_2 : (m,m':Map) (a:ad) (y:A)
    (MapGet m a)=NONE -> (MapGet m' a)=(SOME y) -> 
      (MapGet (MapDelta m m') a)=(SOME y).
  Proof.
    Induction m. Trivial.
    Exact MapDelta_semantics_2_1.
    Induction m'. Intros. Discriminate H2.
    Intros. Rewrite (MapDelta_semantics_comm (M2 m0 m1) (M1 a a0) a1).
    Apply MapDelta_semantics_2_2; Assumption.
    Intros. Simpl. Rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    Rewrite MapGet_M2_bit_0_if. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H5. Rewrite H5.
    Apply H0. Rewrite <- (MapGet_M2_bit_0_1 a H5 m0 m1). Assumption.
    Rewrite <- (MapGet_M2_bit_0_1 a H5 m2 m3). Assumption.
    Intro H5. Rewrite H5. Apply H. Rewrite <- (MapGet_M2_bit_0_0 a H5 m0 m1). Assumption.
    Rewrite <- (MapGet_M2_bit_0_0 a H5 m2 m3). Assumption.
  Qed.

  Lemma MapDelta_semantics_3_1 : (a0:ad) (y0:A) (m':Map) (a:ad) (y,y':A)
    (MapGet (M1 a0 y0) a)=(SOME y) -> (MapGet m' a)=(SOME y') ->
      (MapGet (MapDelta (M1 a0 y0) m') a)=NONE.
  Proof.
    Intros. Unfold MapDelta. Elim (sumbool_of_bool (ad_eq a0 a)). Intro H1.
    Rewrite (ad_eq_complete a0 a H1). Rewrite H0. Rewrite (MapRemove_semantics m' a a).
    Rewrite (ad_eq_correct a). Reflexivity.
    Intro H1. Rewrite (M1_semantics_2 a0 a y0 H1) in H. Discriminate H.
  Qed.

  Lemma MapDelta_semantics_3 : (m,m':Map) (a:ad) (y,y':A)
    (MapGet m a)=(SOME y) -> (MapGet m' a)=(SOME y') -> 
      (MapGet (MapDelta m m') a)=NONE.
  Proof.
    Induction m. Intros. Discriminate H.
    Exact MapDelta_semantics_3_1.
    Induction m'. Intros. Discriminate H2.
    Intros. Rewrite (MapDelta_semantics_comm (M2 m0 m1) (M1 a a0) a1).
    Exact (MapDelta_semantics_3_1 a a0 (M2 m0 m1) a1 y' y H2 H1).
    Intros. Simpl. Rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    Rewrite MapGet_M2_bit_0_if. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H5. Rewrite H5.
    Apply (H0 m3 (ad_div_2 a) y y'). Rewrite <- (MapGet_M2_bit_0_1 a H5 m0 m1). Assumption.
    Rewrite <- (MapGet_M2_bit_0_1 a H5 m2 m3). Assumption.
    Intro H5. Rewrite H5. Apply (H m2 (ad_div_2 a) y y').
    Rewrite <- (MapGet_M2_bit_0_0 a H5 m0 m1). Assumption.
    Rewrite <- (MapGet_M2_bit_0_0 a H5 m2 m3). Assumption.
  Qed.

  Lemma MapDelta_semantics : (m,m':Map)
      (eqm (MapGet (MapDelta m m'))
           [a0:ad] Cases (MapGet m a0) (MapGet m' a0) of
	               NONE (SOME y') => (SOME y')
		     | (SOME y) NONE => (SOME y)
		     | _ _ => NONE
		   end).
  Proof.
    Unfold eqm. Intros. Elim (option_sum (MapGet m' a)). Intro H. Elim H. Intros a0 H0.
    Rewrite H0. Elim (option_sum (MapGet m a)). Intro H1. Elim H1. Intros a1 H2. Rewrite H2.
    Exact (MapDelta_semantics_3 m m' a a1 a0 H2 H0).
    Intro H1. Rewrite H1. Exact (MapDelta_semantics_2 m m' a a0 H1 H0).
    Intro H. Rewrite H. Elim (option_sum (MapGet m a)). Intro H0. Elim H0. Intros a0 H1.
    Rewrite H1. Rewrite (MapDelta_semantics_comm m m' a).
    Exact (MapDelta_semantics_2 m' m a a0 H H1).
    Intro H0. Rewrite H0. Exact (MapDelta_semantics_1 m m' a H0 H).
  Qed.

  Definition MapEmptyp := [m:Map]
    Cases m of
      	M0 => true
      | _ => false
    end.

  Lemma MapEmptyp_correct : (MapEmptyp M0)=true.
  Proof.
    Reflexivity.
  Qed.

  Lemma MapEmptyp_complete : (m:Map) (MapEmptyp m)=true -> m=M0.
  Proof.
    Induction m; Trivial. Intros. Discriminate H.
    Intros. Discriminate H1.
  Qed.

  (** [MapSplit] not implemented: not the preferred way of recursing over Maps
      (use [MapSweep], [MapCollect], or [MapFold] in Mapiter.v. *)

End MapDefs.
