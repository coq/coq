
(*s The decision procedure is instantiated for Z *)

Require cgraph.
Require ZArith.
Require Addr.
Require Addec.

Inductive ZCGForm : Set :=
      ZCGle : ad -> ad -> ZCGForm (* x<=y *)
    | ZCGge : ad -> ad -> ZCGForm (* x>=y *)
    | ZCGlt : ad -> ad -> ZCGForm (* x<y *)
    | ZCGgt : ad -> ad -> ZCGForm (* x>y *)
    | ZCGlep : ad -> ad -> Z -> ZCGForm (* x<=y+k *)
    | ZCGgep : ad -> ad -> Z -> ZCGForm (* x>=y+k *)
    | ZCGltp : ad -> ad -> Z -> ZCGForm (* x<y+k *)
    | ZCGgtp : ad -> ad -> Z -> ZCGForm (* x>y+k *)
    | ZCGlem : ad -> ad -> Z -> ZCGForm (* x+k<=y *)
    | ZCGgem : ad -> ad -> Z -> ZCGForm (* x+k>=y *)
    | ZCGltm : ad -> ad -> Z -> ZCGForm (* x+k<y *)
    | ZCGgtm : ad -> ad -> Z -> ZCGForm (* x+k>y *)
    | ZCGlepm : ad -> ad -> Z -> Z -> ZCGForm (* x+k<=y+k' *)
    | ZCGgepm : ad -> ad -> Z -> Z -> ZCGForm (* x+k>=y+k' *)
    | ZCGltpm : ad -> ad -> Z -> Z -> ZCGForm (* x+k<y+k' *)
    | ZCGgtpm : ad -> ad -> Z -> Z -> ZCGForm (* x+k>y+k' *)
    | ZCGeq : ad -> ad -> ZCGForm (* x=y *)
    | ZCGeqp : ad -> ad -> Z -> ZCGForm (* x=y+k *)
    | ZCGeqm : ad -> ad -> Z -> ZCGForm (* x+k=y *)
    | ZCGeqpm : ad -> ad -> Z -> Z -> ZCGForm (* x+k=y+k' *)
    | ZCGzylem : ad -> Z -> ZCGForm (* k<=y *)
    | ZCGzygem : ad -> Z -> ZCGForm (* k>=y *)
    | ZCGzyltm : ad -> Z -> ZCGForm (* k<y *)
    | ZCGzygtm : ad -> Z -> ZCGForm (* k>y *)
    | ZCGzylepm : ad -> Z -> Z -> ZCGForm (* k<=y+k' *)
    | ZCGzygepm : ad -> Z -> Z -> ZCGForm (* k>=y+k' *)
    | ZCGzyltpm : ad -> Z -> Z -> ZCGForm (* k<y+k' *)
    | ZCGzygtpm : ad -> Z -> Z -> ZCGForm (* k>y+k' *)
    | ZCGzyeqm : ad -> Z -> ZCGForm (* k=y *)
    | ZCGzyeqpm : ad -> Z -> Z -> ZCGForm (* k=y+k' *)
    | ZCGxzlep : ad -> Z -> ZCGForm (* x<=k *)
    | ZCGxzgep : ad -> Z -> ZCGForm (* x>=k *)
    | ZCGxzltp : ad -> Z -> ZCGForm (* x<k *)
    | ZCGxzgtp : ad -> Z -> ZCGForm (* x>k *)
    | ZCGxzlepm : ad -> Z -> Z -> ZCGForm (* x+k<=k' *)
    | ZCGxzgepm : ad -> Z -> Z -> ZCGForm (* x+k>=k' *)
    | ZCGxzltpm : ad -> Z -> Z -> ZCGForm (* x+k<k' *)
    | ZCGxzgtpm : ad -> Z -> Z -> ZCGForm (* x+k>k' *)
    | ZCGxzeqp : ad -> Z -> ZCGForm (* x=k *)
    | ZCGxzeqpm : ad -> Z -> Z -> ZCGForm (* x+k=k' *)
    | ZCGzzlep : Z -> Z -> ZCGForm (* k<=k' *)
    | ZCGzzltp : Z -> Z -> ZCGForm (* k<k' *)
    | ZCGzzgep : Z -> Z -> ZCGForm (* k>=k' *)
    | ZCGzzgtp : Z -> Z -> ZCGForm (* k>k' *)
    | ZCGzzeq : Z -> Z -> ZCGForm (* k=k' *)
    | ZCGand : ZCGForm -> ZCGForm -> ZCGForm
    | ZCGor : ZCGForm -> ZCGForm -> ZCGForm
    | ZCGimp : ZCGForm -> ZCGForm -> ZCGForm
    | ZCGnot : ZCGForm -> ZCGForm
    | ZCGiff : ZCGForm -> ZCGForm -> ZCGForm.

Definition ZCG_eval := (CGeval Z Zplus Zle_bool).

(*s Translation of formula on Z into a constraint graph formula. 
    we reserve [ad_z] as the "zero" variable, 
    i.e., the one that is anchored at the value `0`. *)

Fixpoint ZCGtranslate [f:ZCGForm] : (CGForm Z) :=
  Cases f of
      (ZCGle x y) => (CGleq Z x y `0`)
    | (ZCGge x y) => (CGleq Z y x `0`)
    | (ZCGlt x y) => (CGleq Z x y `-1`)
    | (ZCGgt x y) => (CGleq Z y x `-1`)
    | (ZCGlep x y k) => (CGleq Z x y k)
    | (ZCGgep x y k) => (CGleq Z y x (Zopp k))
    | (ZCGltp x y k) => (CGleq Z x y `k-1`)
    | (ZCGgtp x y k) => (CGleq Z y x (Zopp `k+1`))
    | (ZCGlem x y k) => (CGleq Z x y (Zopp k))
    | (ZCGgem x y k) => (CGleq Z y x k)
    | (ZCGltm x y k) => (CGleq Z x y (Zopp `k+1`))
    | (ZCGgtm x y k) => (CGleq Z y x `k-1`)
    | (ZCGlepm x y k k') => (CGleq Z x y `k'-k`)
    | (ZCGgepm x y k k') => (CGleq Z y x `k-k'`)
    | (ZCGltpm x y k k') => (CGleq Z x y `k'-k-1`)
    | (ZCGgtpm x y k k') => (CGleq Z y x `k-k'-1`)
    | (ZCGeq x y) => (CGeq Z x y `0`)
    | (ZCGeqp x y k) => (CGeq Z x y k)
    | (ZCGeqm x y k) => (CGeq Z y x k)
    | (ZCGeqpm x y k k') => (CGeq Z x y `k'-k`)
    | (ZCGzylem y k) => (CGleq Z ad_z y (Zopp k)) 
    | (ZCGzygem y k) => (CGleq Z y ad_z k) 
    | (ZCGzyltm y k) => (CGleq Z ad_z y (Zopp `k+1`))
    | (ZCGzygtm y k) => (CGleq Z y ad_z `k-1`)
    | (ZCGzylepm y k k') => (CGleq Z ad_z y `k'-k`)
    | (ZCGzygepm y k k') => (CGleq Z y ad_z `k-k'`)
    | (ZCGzyltpm y k k') => (CGleq Z ad_z y `k'-k-1`)
    | (ZCGzygtpm y k k') => (CGleq Z y ad_z `k-k'-1`)
    | (ZCGzyeqm y k) => (CGeq Z y ad_z k)
    | (ZCGzyeqpm y k k') => (CGeq Z y ad_z `k-k'`)
    | (ZCGxzlep x k) => (CGleq Z x ad_z k)
    | (ZCGxzgep x k) => (CGleq Z ad_z x (Zopp k))
    | (ZCGxzltp x k) => (CGleq Z x ad_z `k-1`)
    | (ZCGxzgtp x k) => (CGleq Z ad_z x (Zopp `k+1`))
    | (ZCGxzlepm x k k') => (CGleq Z x ad_z `k'-k`)
    | (ZCGxzgepm x k k') => (CGleq Z ad_z x `k-k'`)
    | (ZCGxzltpm x k k') => (CGleq Z x ad_z `k'-k-1`)
    | (ZCGxzgtpm x k k') => (CGleq Z ad_z x `k-k'-1`)
    | (ZCGxzeqp x k) => (CGeq Z x ad_z k)
    | (ZCGxzeqpm x k k') => (CGeq Z x ad_z `k'-k`)
    | (ZCGzzlep k k') => (CGleq Z ad_z ad_z `k'-k`)
    | (ZCGzzltp k k') => (CGleq Z ad_z ad_z `k'-k-1`)
    | (ZCGzzgep k k') => (CGleq Z ad_z ad_z `k-k'`)
    | (ZCGzzgtp k k') => (CGleq Z ad_z ad_z `k-k'-1`)
    | (ZCGzzeq k k') => (CGeq Z ad_z ad_z `k-k'`)
    | (ZCGand f0 f1) => (CGand Z (ZCGtranslate f0) (ZCGtranslate f1))
    | (ZCGor f0 f1) => (CGor Z (ZCGtranslate f0) (ZCGtranslate f1))
    | (ZCGimp f0 f1) => (CGimp Z (ZCGtranslate f0) (ZCGtranslate f1))
    | (ZCGnot f0) => (CGnot Z (ZCGtranslate f0))
    | (ZCGiff f0 f1) => (CGand Z (CGimp Z (ZCGtranslate f0) (ZCGtranslate f1))
                                 (CGimp Z (ZCGtranslate f1) (ZCGtranslate f0)))
  end.

Section ZCGevalDef.

  Variable rho : ad -> Z.

Fixpoint ZCGeval [f:ZCGForm] : Prop :=
    Cases f of
      (ZCGle x y) => `(rho x)<=(rho y)`
    | (ZCGge x y) => `(rho x)>=(rho y)`
    | (ZCGlt x y) => `(rho x)<(rho y)`
    | (ZCGgt x y) => `(rho x)>(rho y)`
    | (ZCGlep x y k) => `(rho x)<=(rho y)+k`
    | (ZCGgep x y k) => `(rho x)>=(rho y)+k`
    | (ZCGltp x y k) => `(rho x)<(rho y)+k`
    | (ZCGgtp x y k) => `(rho x)>(rho y)+k`
    | (ZCGlem x y k) => `(rho x)+k<=(rho y)`
    | (ZCGgem x y k) => `(rho x)+k>=(rho y)`
    | (ZCGltm x y k) => `(rho x)+k<(rho y)`
    | (ZCGgtm x y k) => `(rho x)+k>(rho y)`
    | (ZCGlepm x y k k') => `(rho x)+k<=(rho y)+k'`
    | (ZCGgepm x y k k') => `(rho x)+k>=(rho y)+k'`
    | (ZCGltpm x y k k') => `(rho x)+k<(rho y)+k'`
    | (ZCGgtpm x y k k') => `(rho x)+k>(rho y)+k'`
    | (ZCGeq x y) => `(rho x)=(rho y)`
    | (ZCGeqp x y k) => `(rho x)=(rho y)+k`
    | (ZCGeqm x y k) => `(rho x)+k=(rho y)`
    | (ZCGeqpm x y k k') => `(rho x)+k=(rho y)+k'`
    | (ZCGzylem y k) => `k<=(rho y)`
    | (ZCGzygem y k) => `k>=(rho y)`
    | (ZCGzyltm y k) => `k<(rho y)`
    | (ZCGzygtm y k) => `k>(rho y)`
    | (ZCGzylepm y k k') => `k<=(rho y)+k'`
    | (ZCGzygepm y k k') => `k>=(rho y)+k'`
    | (ZCGzyltpm y k k') => `k<(rho y)+k'`
    | (ZCGzygtpm y k k') => `k>(rho y)+k'`
    | (ZCGzyeqm y k) => `k=(rho y)`
    | (ZCGzyeqpm y k k') => `k=(rho y)+k'`
    | (ZCGxzlep x k) => `(rho x)<=k`
    | (ZCGxzgep x k) => `(rho x)>=k`
    | (ZCGxzltp x k) => `(rho x)<k`
    | (ZCGxzgtp x k) => `(rho x)>k`
    | (ZCGxzlepm x k k') => `(rho x)+k<=k'`
    | (ZCGxzgepm x k k') => `(rho x)+k>=k'`
    | (ZCGxzltpm x k k') => `(rho x)+k<k'`
    | (ZCGxzgtpm x k k') => `(rho x)+k>k'`
    | (ZCGxzeqp x k) => `(rho x)=k`
    | (ZCGxzeqpm x k k') => `(rho x)+k=k'`
    | (ZCGzzlep k k') => `k<=k'`
    | (ZCGzzltp k k') => `k<k'`
    | (ZCGzzgep k k') => `k>=k'`
    | (ZCGzzgtp k k') => `k>k'`
    | (ZCGzzeq k k') => `k=k'`
    | (ZCGand f0 f1) => (ZCGeval f0) /\ (ZCGeval f1)
    | (ZCGor f0 f1) => (ZCGeval f0) \/ (ZCGeval f1)
    | (ZCGimp f0 f1) => (ZCGeval f0) -> (ZCGeval f1)
    | (ZCGnot f0) => ~(ZCGeval f0)
    | (ZCGiff f0 f1) => (ZCGeval f0) <-> (ZCGeval f1)
  end.

  Variable Zrho_zero : (rho ad_z)=ZERO.

Lemma ZCGeval_correct 
  : (f:ZCGForm) (ZCGeval f) <-> (ZCG_eval rho (ZCGtranslate f)).
  Proof.
    Induction f; Simpl. Intros. Rewrite Zero_right. Apply Zle_is_le_bool.
    Intros. Rewrite Zero_right. Apply Zge_is_le_bool.
    Intros. Exact (Zlt_is_le_bool (rho a) (rho a0)).
    Intros. Exact (Zgt_is_le_bool (rho a) (rho a0)).
    Intros. Apply Zle_is_le_bool.
    Intros. Apply iff_trans with b:=`(rho a0)+z <= (rho a)`. Apply Zge_iff_le.
    Apply iff_trans with b:=`(rho a0) <= (rho a)-z`. Apply Zle_plus_swap.
    Unfold Zminus. Apply Zle_is_le_bool.
    Intros. Apply iff_trans with b:=(Zle_bool (rho a) `(rho a0)+z-1`)=true. Apply Zlt_is_le_bool.
    Unfold 1 Zminus. Rewrite Zplus_assoc_r. Split; Intro; Assumption.
    Intros. Apply iff_trans with b:=`(rho a0)+z < (rho a)`. Apply Zgt_iff_lt.
    Apply iff_trans with `(rho a0) < (rho a)-z`. Apply Zlt_plus_swap.
    Rewrite Zopp_Zplus. Rewrite Zplus_assoc_l. Exact (Zlt_is_le_bool (rho a0) `(rho a)-z`).
    Intros. Apply iff_trans with b:=`(rho a) <= (rho a0)-z`. Apply Zle_plus_swap.
    Unfold Zminus. Apply Zle_is_le_bool.
    Intros. Apply Zge_is_le_bool.
    Intros. Apply iff_trans with b:=`(rho a) < (rho a0)-z`. Apply Zlt_plus_swap.
    Rewrite Zopp_Zplus. Rewrite Zplus_assoc_l. Exact (Zlt_is_le_bool (rho a) `(rho a0)-z`).
    Intros. Unfold Zminus. Rewrite Zplus_assoc_l. Exact (Zgt_is_le_bool `(rho a)+z` (rho a0)).
    Intros. Apply iff_trans with b:=`(rho a) <= (rho a0)+z0-z`. Apply Zle_plus_swap.
    Unfold 1 Zminus. Rewrite Zplus_assoc_r. Unfold Zminus. Apply Zle_is_le_bool.
    Intros. Apply iff_trans with b:=`(rho a0)+z0 <= (rho a)+z`. Apply Zge_iff_le.
    Apply iff_trans with b:=`(rho a0) <= (rho a)+z-z0`. Apply Zle_plus_swap.
    Unfold 1 Zminus. Rewrite Zplus_assoc_r. Unfold Zminus. Apply Zle_is_le_bool.
    Intros. Apply iff_trans with b:=`(rho a) < (rho a0)+z0-z`. Apply Zlt_plus_swap.
    Unfold 2 Zminus. Rewrite Zplus_assoc_l. Unfold 1 Zminus. Rewrite Zplus_assoc_r.
    Exact (Zlt_is_le_bool (rho a) `(rho a0)+(z0+ -z)`).
    Intros. Apply iff_trans with b:=`(rho a0)+z0 < (rho a)+z`. Apply Zgt_iff_lt.
    Apply iff_trans with b:=`(rho a0) < (rho a)+z-z0`. Apply Zlt_plus_swap.
    Unfold 2 Zminus. Rewrite Zplus_assoc_l. Unfold 1 Zminus. Rewrite Zplus_assoc_r.
    Exact (Zlt_is_le_bool (rho a0) `(rho a)+(z+ -z0)`).
    Intros. Rewrite Zero_right. Split; Intro; Assumption.
    Split; Intro; Assumption.
    Split; Intro; Apply sym_eq; Assumption.
    Intros. Unfold Zminus. Rewrite Zplus_assoc_l. Exact (Zeq_plus_swap (rho a) `(rho a0)+z0` z).
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z <= (rho a)`. Rewrite Zero_left.
    Split; Intro; Assumption.
    Apply iff_trans with b:=`0 <= (rho a)-z`. Apply Zle_plus_swap.
    Unfold Zminus. Apply Zle_is_le_bool.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply Zge_is_le_bool.
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z < (rho a)`. Rewrite Zero_left.
    Split; Intro; Assumption.
    Apply iff_trans with b:=`0 < (rho a)-z`. Apply Zlt_plus_swap.
    Rewrite Zopp_Zplus. Rewrite Zplus_assoc_l. Exact (Zlt_is_le_bool `0` `(rho a)-z`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply Zgt_is_le_bool.
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z <= (rho a)+z0`. Rewrite Zero_left.
    Split; Intro; Assumption.
    Apply iff_trans with b:=`0 <= (rho a)+z0-z`. Apply Zle_plus_swap.
    Unfold 2 Zminus. Rewrite Zplus_assoc_l. Exact (Zle_is_le_bool `0` `(rho a)+z0-z`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`(rho a)+z0 <= z`.
    Apply Zge_iff_le.
    Apply iff_trans with b:=`(rho a) <= z-z0`. Apply Zle_plus_swap.
    Apply Zle_is_le_bool.
    Rewrite Zrho_zero. Intros. Apply iff_trans with `0+z < (rho a)+z0`. Rewrite Zero_left.
    Split; Intro; Assumption.
    Apply iff_trans with b:=`0 < (rho a)+z0-z`. Apply Zlt_plus_swap.
    Unfold 2 Zminus. Rewrite Zplus_assoc_l. Unfold Zminus. Rewrite Zplus_assoc_l.
    Exact (Zlt_is_le_bool `0` `(rho a)+z0+ -z`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`(rho a)+z0 < z`.
    Apply Zgt_iff_lt.
    Apply iff_trans with b:=`(rho a) < z-z0`. Apply Zlt_plus_swap.
    Apply Zlt_is_le_bool.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Split; Intro; Apply sym_eq; Assumption.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with `(rho a)+z0 = z`.
    Split; Intro; Apply sym_eq; Assumption.
    Apply Zeq_plus_swap.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply Zle_is_le_bool.
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z <= (rho a)`. Rewrite Zero_left.
    Apply Zge_iff_le.
    Apply iff_trans with b:=`0 <= (rho a)-z`. Apply Zle_plus_swap.
    Exact (Zle_is_le_bool `0` `(rho a)-z`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply Zlt_is_le_bool.
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z < (rho a)`. Rewrite Zero_left.
    Apply Zgt_iff_lt.
    Apply iff_trans with b:=`0 < (rho a)-z`. Apply Zlt_plus_swap.
    Rewrite Zopp_Zplus. Rewrite Zplus_assoc_l. Exact (Zlt_is_le_bool `0` `(rho a)-z`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`(rho a) <= z0-z`.
    Apply Zle_plus_swap.
    Apply Zle_is_le_bool. 
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z0 <= (rho a)+z`. Rewrite Zero_left.
    Apply Zge_iff_le.
    Apply iff_trans with b:=`0 <= (rho a)+z-z0`. Apply Zle_plus_swap.
    Unfold 2 Zminus. Rewrite Zplus_assoc_l. Exact (Zle_is_le_bool `0` `(rho a)+z-z0`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`(rho a) < z0-z`.
    Apply Zlt_plus_swap.
    Apply Zlt_is_le_bool.
    Rewrite Zrho_zero. Intros. Apply iff_trans with b:=`0+z0 < (rho a)+z`. Rewrite Zero_left.
    Apply Zgt_iff_lt.
    Apply iff_trans with b:=`0 < (rho a)+z-z0`. Apply Zlt_plus_swap.
    Unfold 2 Zminus. Rewrite Zplus_assoc_l. Unfold Zminus. Rewrite Zplus_assoc_l.
    Exact (Zlt_is_le_bool `0` `(rho a)+z+ -z0`).
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Split; Intro; Assumption.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply Zeq_plus_swap.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`0+z <= z0`.
    Rewrite Zero_left. Split; Intro; Assumption.
    Apply iff_trans with b:=`0 <= z0-z`. Apply Zle_plus_swap.
    Apply Zle_is_le_bool.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`0+z < z0`.
    Rewrite Zero_left. Split; Intro; Assumption.
    Apply iff_trans with b:=`0 < z0-z`. Apply Zlt_plus_swap.
    Apply Zlt_is_le_bool.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`0+z0 <= z`.
    Rewrite Zero_left. Apply Zge_iff_le.
    Apply iff_trans with b:=`0 <= z-z0`. Apply Zle_plus_swap.
    Apply Zle_is_le_bool.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Apply iff_trans with b:=`0+z0 < z`.
    Rewrite Zero_left. Apply Zgt_iff_lt.
    Apply iff_trans with b:=`0 < z-z0`. Apply Zlt_plus_swap.
    Apply Zlt_is_le_bool.
    Rewrite Zrho_zero. Intros. Rewrite Zero_left. Split. Intro. Rewrite H. Apply Zminus_n_n.
    Intro. Rewrite <- (Zero_left z0). Rewrite H. Unfold Zminus. Rewrite Zplus_assoc_r.
    Rewrite Zplus_inverse_l. Rewrite Zero_right. Reflexivity.
    Intros. Elim H. Intros. Elim H0. Intros. Split. Intro. Elim H5. Intros. Split. Apply H1.
    Assumption.
    Apply H3. Assumption.
    Intro. Elim H5. Intros. Split. Apply H2. Assumption.
    Apply H4. Assumption.
    Intros. Elim H. Intros. Elim H0. Intros. Split. Intro. Elim H5. Intro. Left . Apply H1.
    Assumption.
    Intro. Right . Apply H3. Assumption.
    Intro. Elim H5. Intro. Left . Apply H2. Assumption.
    Intro. Right . Apply H4. Assumption.
    Intros. Elim H. Intros. Elim H0. Intros. Split. Intros. Apply H3. Apply H5. Apply H2.
    Assumption.
    Intros. Apply H4. Apply H5. Apply H1. Assumption.
    Unfold not. Intros. Elim H. Intros. Split. Intros. Apply H2. Apply H1. Assumption.
    Intros. Apply H2. Apply H0. Assumption.
    Intros. Fold (ZCG_eval rho (ZCGtranslate z))<->(ZCG_eval rho (ZCGtranslate z0)). Split.
    Intro. Apply iff_trans with b:=(ZCGeval z). Apply iff_sym. Assumption.
    Apply iff_trans with b:=(ZCGeval z0). Assumption.
    Assumption.
    Intro. Apply iff_trans with b:=(ZCG_eval rho (ZCGtranslate z)). Assumption.
    Apply iff_trans with b:=(ZCG_eval rho (ZCGtranslate z0)). Assumption.
    Apply iff_sym. Assumption.
  Qed.

End ZCGevalDef.

Definition ZCG_solve 
 := [f:ZCGForm] (CG_solve Z ZERO Zplus Zopp Zle_bool `1` (ZCGtranslate f)).

Theorem ZCG_solve_correct :
      	(f:ZCGForm) (ZCG_solve f)=true ->
          {rho:ad->Z | (ZCGeval rho f) /\ (rho ad_z)=`0`}.
Proof.
  Intros.
  Elim (CG_solve_correct_anchored Z ZERO Zplus Zopp Zle_bool Zero_right
       Zero_left Zplus_assoc_r Zplus_inverse_r Zle_bool_refl
       Zle_bool_antisym Zle_bool_trans Zle_bool_total
       Zle_bool_plus_mono `1` Zone_pos Zone_min_pos ad_z `0` ? H).
  Intros rho H0. Split with rho. Elim H0. Intros. Split.
  Apply (proj2 ? ? (ZCGeval_correct rho H2 f)). Assumption.
  Assumption.
Qed.

Theorem ZCG_solve_complete
   : (f:ZCGForm) (rho:ad->Z) 
     (ZCGeval rho f) -> (rho ad_z)=`0` -> (ZCG_solve f)=true.
Proof.
  Intros. Unfold ZCG_solve.
  Apply (CG_solve_complete Z ZERO Zplus Zopp Zle_bool Zero_right
        Zero_left Zplus_assoc_r Zplus_inverse_r Zle_bool_refl
        Zle_bool_antisym Zle_bool_trans Zle_bool_total
        Zle_bool_plus_mono `1` Zone_pos Zone_min_pos (ZCGtranslate f)
        rho).
  Apply (proj1 ? ? (ZCGeval_correct rho H0 f)). Assumption.
Qed.

Definition ZCG_prove 
  := [f:ZCGForm] (CG_prove Z ZERO Zplus Zopp Zle_bool `1` (ZCGtranslate f)).

Theorem ZCG_prove_correct 
  : (f:ZCGForm) (ZCG_prove f)=true ->
    (rho:ad->Z) (rho ad_z)=`0` -> (ZCGeval rho f).
Proof.
  Intros. Apply (proj2 ? ? (ZCGeval_correct rho H0 f)).
  Exact (CG_prove_correct Z ZERO Zplus Zopp Zle_bool Zero_right Zero_left
        Zplus_assoc_r Zplus_inverse_r Zle_bool_refl Zle_bool_antisym
        Zle_bool_trans Zle_bool_total Zle_bool_plus_mono `1` Zone_pos
        Zone_min_pos ? H rho).
Qed.

Theorem ZCG_prove_complete 
  : (f:ZCGForm)
    ((rho:ad->Z) (rho ad_z)=`0` -> (ZCGeval rho f)) -> (ZCG_prove f)=true.
Proof.
  Intros. Unfold ZCG_prove.
  Apply (CG_prove_complete_anchored Z ZERO Zplus Zopp Zle_bool Zero_right
        Zero_left Zplus_assoc_r Zplus_inverse_r Zle_bool_refl
        Zle_bool_antisym Zle_bool_trans Zle_bool_total
        Zle_bool_plus_mono `1` Zone_pos Zone_min_pos (ZCGtranslate f)
        ad_z `0`).
  Intros. Exact (proj1 ? ? (ZCGeval_correct rho H0 f) (H rho H0)).
Qed.

(*i Tests:

  Definition v := [n:Z] Cases n of
                            (POS p) => (ad_x p)
			  | _ => ad_z
			end.

  Lemma test1 : (x,y:Z) `x<=y` -> `x<=y+1`.
  Proof.
    Intros.
    Cut (rho:ad->Z) (rho ad_z)=`0` ->
          (ZCGeval rho (ZCGimp (ZCGle (v`1`) (v`2`)) (ZCGlep (v`1`) (v`2`) `1`))).
    Intro.
    Exact (H0 [a:ad]Case (ad_eq a (v`1`)) of x
                    Case (ad_eq a (v`2`)) of y
                    `0` end end
              (refl_equal ? ?)
              H).

    Intros. Apply ZCG_prove_correct. Compute. Reflexivity.
    Assumption.
   Qed.

  Lemma test2 : (x,y:Z) ~(`x<=y` -> `x<=y-1`).
  Proof.
    Intros.
    Cut (rho:ad->Z) (rho ad_z)=`0` ->
          (ZCGeval rho (ZCGnot (ZCGimp (ZCGle (v `1`) (v `2`)) (ZCGlep (v `1`) (v `2`) `-1`)))).
    Intro.
    Exact (H [a:ad] Case (ad_eq a (v `1`)) of x
                    Case (ad_eq a (v `2`)) of y
                    `0` end end (refl_equal ? ?)).
    Intros. Apply ZCG_prove_correct. Compute. (* fails: remains to prove false=true; indeed,
    test2 is not provable. *)
    <Your Tactic Text here>
    <Your Tactic Text here>

i*)
