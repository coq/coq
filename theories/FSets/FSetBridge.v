(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** This module implements bridges (as functors) from dependent
    to/from non-dependent set signature. *)

Require Export FSetInterface.
Set Implicit Arguments.

(** * From non-dependent signature [S] to dependent signature [Sdep]. *)

Module DepOfNodep [M:S] <: Sdep with Module E := M.E.
  Import M.

  Module ME := MoreOrderedType E.
   
  Definition empty: { s:t | Empty s }.
  Proof. 
    Exists empty; Auto.
  Save.

  Definition is_empty: (s:t){ Empty s }+{ ~(Empty s) }.
  Proof. 
    Intros; Generalize (!is_empty_1 s) (!is_empty_2 s).
    Case (is_empty s); Intuition.
  Save.


  Definition mem : (x:elt) (s:t) { (In x s) } + { ~(In x s) }.
  Proof. 
    Intros; Generalize (!mem_1 s x) (!mem_2 s x).
    Case (mem x s); Intuition.
  Save.
 
  Definition add : (x:elt) (s:t){ s':t | (Add x s s') }.
  Proof.
    Intros; Exists (add x s); Auto.
    Unfold Add; Intuition.
    Elim (ME.eq_dec x y); Auto.
    Intros; Right. 
    EApply add_3; EAuto.
    Apply In_1 with x; Auto.
  Save. 
 
  Definition singleton : (x:elt){ s:t | (y:elt)(In y s) <-> (E.eq x y)}.
  Proof. 
    Intros; Exists (singleton x); Intuition.
  Save.
 
  Definition remove : (x:elt)(s:t)
                     { s':t | (y:elt)(In y s') <-> (~(E.eq y x) /\ (In y s))}.
  Proof.
    Intros; Exists (remove x s); Intuition.
    Absurd (In x (remove x s)); Auto.
    Apply In_1 with y; Auto. 
    Elim (ME.eq_dec x y); Intros; Auto.
    Absurd (In x (remove x s)); Auto.
    Apply In_1 with y; Auto. 
    EAuto.
  Save.

  Definition union : (s,s':t)
                    { s'':t | (x:elt)(In x s'') <-> ((In x s)\/(In x s'))}.
  Proof.
    Intros; Exists (union s s'); Intuition.
  Save.    

  Definition inter : (s,s':t)
                    { s'':t | (x:elt)(In x s'') <-> ((In x s)/\(In x s'))}.
  Proof. 
    Intros; Exists (inter s s'); Intuition; EAuto.
  Save.

  Definition diff : (s,s':t)
                    { s'':t | (x:elt)(In x s'') <-> ((In x s)/\~(In x s'))}.
  Proof. 
    Intros; Exists (diff s s'); Intuition; EAuto. 
    Absurd (In x s'); EAuto. 
  Save. 
 
  Definition equal : (s,s':t){ Equal s s' } + { ~(Equal s s') }.
  Proof. 
    Intros. 
    Generalize (!equal_1 s s') (!equal_2 s s').
    Case (equal s s');Intuition.
  Save.

  Definition subset : (s,s':t) { Subset s s' } + { ~(Subset s s') }.
  Proof. 
    Intros. 
    Generalize (!subset_1 s s') (!subset_2 s s').
    Case (subset s s');Intuition.
  Save.   

  Definition fold :
   (A:Set)(f:elt->A->A)(s:t)(i:A) 
   { r : A | (EX l:(list elt) | 
                  (Unique E.eq l) /\
                  ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
                  r = (fold_right f i l)) }.
  Proof.
    Intros; Exists (!fold A f s i); Exact (fold_1 s i f).
  Save.  

  Definition cardinal :
    (s:t) { r : nat | (EX l:(list elt) | 
                              (Unique E.eq l) /\ 
                              ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
                              r = (length l)) }.
  Proof.
    Intros; Exists (cardinal s); Exact (cardinal_1 s).
  Save.    

  Definition fdec := 
    [P:elt->Prop; Pdec:(x:elt){P x}+{~(P x)}; x:elt] 
    if (Pdec x) then [_]true else [_]false. 

  Lemma compat_P_aux : 
	(P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(compat_P E.eq P) -> 
        (compat_bool E.eq (fdec Pdec)).
  Proof.
    Unfold compat_P compat_bool fdec; Intros.
    Generalize (E.eq_sym H0); Case (Pdec x); Case (Pdec y); Ground.
  Qed.

  Hints Resolve compat_P_aux.

  Definition filter : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { s':t | (compat_P E.eq P) -> (x:elt)(In x s') <-> ((In x s)/\(P x)) }.
  Proof.
    Intros. 
    Exists (filter (fdec Pdec) s).
    Intro H; Assert (compat_bool E.eq (fdec Pdec)); Auto.
    Intuition.
    EAuto.
    Generalize (filter_2 H0 H1).
    Unfold fdec.
    Case (Pdec x); Intuition.
    Inversion H2.
    Apply filter_3; Auto.
    Unfold fdec; Simpl.
    Case (Pdec x); Intuition.
  Save.

  Definition for_all : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { (compat_P E.eq P) -> (For_all P s) } + 
     { (compat_P E.eq P) -> ~(For_all P s) }.
  Proof. 
    Intros. 
    Generalize (!for_all_1 s (fdec Pdec)) (!for_all_2 s (fdec Pdec)).
    Case (for_all (fdec Pdec) s); Unfold For_all; [Left|Right]; Intros.
    Assert (compat_bool E.eq (fdec Pdec)); Auto.
    Generalize (H0 H3 (refl_equal ??) ? H2).
    Unfold fdec. 
    Case (Pdec x); Intuition.
    Inversion H4.
    Intuition.    
    Absurd false=true; [Auto with bool|Apply H; Auto].
    Intro.
    Unfold fdec. 
    Case (Pdec x); Intuition.
  Save.

  Definition exists : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { (compat_P E.eq P) -> (Exists P s) } + 
     { (compat_P E.eq P) -> ~(Exists P s) }.
  Proof. 
    Intros. 
    Generalize (!exists_1 s (fdec Pdec)) (!exists_2 s (fdec Pdec)).
    Case (exists (fdec Pdec) s); Unfold Exists; [Left|Right]; Intros.
    Elim H0; Auto; Intros.
    Exists x; Intuition.
    Generalize H4.
    Unfold fdec. 
    Case (Pdec x); Intuition.
    Inversion H2.
    Intuition. 
    Elim H2; Intros.    
    Absurd false=true; [Auto with bool|Apply H; Auto].
    Exists x; Intuition.
    Unfold fdec. 
    Case (Pdec x); Intuition.
  Save.

  Definition partition : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { partition : t*t |
        let (s1,s2) = partition in
        (compat_P E.eq P) -> 
        ((For_all P s1) /\
         (For_all ([x]~(P x)) s2) /\
         (x:elt)(In x s)<->((In x s1)\/(In x s2))) }.
  Proof.
    Intros.
    Exists (partition (fdec Pdec) s).
    Generalize (!partition_1 s (fdec Pdec)) (!partition_2 s (fdec Pdec)).
    Case (partition (fdec Pdec) s).
    Intros s1 s2; Simpl.
    Intros; Assert (compat_bool E.eq (fdec Pdec)); Auto.
    Intros; Assert (compat_bool E.eq [x](negb (fdec Pdec x))).
    Generalize H2; Unfold compat_bool;Intuition; Apply (f_equal ?? negb); Auto.
    Intuition.
    Generalize H4; Unfold For_all Equal; Intuition.
    Elim (H0 x); Intros.
    Assert (fdec Pdec x)=true.
     EAuto.      
    Generalize H8; Unfold fdec; Case (Pdec x); Intuition.
    Inversion H9.
    Generalize H; Unfold For_all Equal; Intuition.
    Elim (H0 x); Intros.
    Cut ([x](negb (fdec Pdec x)) x)=true. 
    Unfold fdec; Case (Pdec x); Intuition.
      Change ([x](negb (fdec Pdec x)) x)=true.
      Apply (!filter_2 s x); Auto.
    LetTac b := (fdec Pdec x); Generalize (refl_equal ? b); 
      Pattern -1 b; Case b; Unfold b; [Left|Right].
    Elim (H4 x); Intros _ B; Apply B; Auto.
    Elim (H x); Intros _ B; Apply B; Auto.
    Apply filter_3; Auto.
    Rewrite H5; Auto.
    EApply (filter_1 1!s 2!x H2); Elim (H4 x); Intros B _; Apply B; Auto.
    EApply (filter_1 1!s 2!x H3); Elim (H x); Intros B _; Apply B; Auto.
  Save. 

  Definition choose : (s:t) {x:elt | (In x s)} + { Empty s }.
  Proof.  
    Intros.
    Generalize (!choose_1 s) (!choose_2 s).
    Case (choose s); [Left|Right]; Auto.
    Exists e; Auto.    
  Save.

  Definition elements : 
     (s:t){ l:(list elt) | (sort E.lt l)/\(x:elt)(In x s)<->(InList E.eq x l)}.
   Proof.
     Intros; Exists (elements s); Intuition.   
   Save. 

  Definition min_elt : 
    (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt y x) s) } + { Empty s }.
  Proof. 
    Intros; Generalize (!min_elt_1 s) (!min_elt_2 s) (!min_elt_3 s).
    Case (min_elt s); [Left|Right]; Auto.    
    Exists e; Unfold For_all; EAuto.
  Save. 

  Definition max_elt : 
    (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt x y) s) } + { Empty s }.
  Proof. 
    Intros; Generalize (!max_elt_1 s) (!max_elt_2 s) (!max_elt_3 s).
    Case (max_elt s); [Left|Right]; Auto.    
    Exists e; Unfold For_all; EAuto.
  Save. 

  Module E:=E. 

  Definition elt := elt.
  Definition t := t.

  Definition In := In. 
  Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
  Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
  Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
  Definition Empty := [s](a:elt)~(In a s).
  Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
  Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).
  
  Definition eq_In := In_1.

  Definition eq := eq.
  Definition lt := lt.
  Definition eq_refl := eq_refl.
  Definition eq_sym := eq_sym.
  Definition eq_trans := eq_trans.
  Definition lt_trans := lt_trans. 
  Definition lt_not_eq := lt_not_eq.
  Definition compare := compare.

End DepOfNodep.


(** * From dependent signature [Sdep] to non-dependent signature [S]. *)

Module NodepOfDep [M:Sdep] <: S with Module E := M.E.
  Import M.

  Module ME := MoreOrderedType E.

  Definition empty : t := let (s,_) = M.empty in s.

  Lemma empty_1 : (Empty empty).
  Proof.
    Unfold empty; Case M.empty; Auto.
  Save.

  Definition is_empty : t -> bool := 
    [s:t]if (M.is_empty s) then [_]true else [_]false.

  Lemma is_empty_1 : (s:t)(Empty s) -> (is_empty s)=true.
  Proof.
    Intros; Unfold is_empty; Case (M.is_empty s); Auto.
  Save.

  Lemma is_empty_2 : (s:t)(is_empty s)=true -> (Empty s).
  Proof.
    Intro s; Unfold is_empty; Case (M.is_empty s); Auto.
    Intros; Discriminate H.
  Save.

  Definition mem : elt -> t -> bool := 
    [x:elt][s:t]if (M.mem x s) then [_]true else [_]false.

  Lemma mem_1 : (s:t)(x:elt)(In x s) -> (mem x s)=true.
  Proof.
    Intros; Unfold mem; Case (M.mem x s); Auto.
  Save.
   
  Lemma mem_2 : (s:t)(x:elt)(mem x s)=true -> (In x s).
  Proof.
    Intros s x; Unfold mem; Case (M.mem x s); Auto.
    Intros; Discriminate H.
  Save.

  Definition equal : t -> t -> bool := 
    [s,s']if (M.equal s s') then [_]true else [_]false.

  Lemma equal_1 : (s,s':t)(Equal s s') -> (equal s s')=true.
  Proof. 
    Intros; Unfold equal; Case M.equal; Intuition.
  Save.    
 
  Lemma equal_2 : (s,s':t)(equal s s')=true -> (Equal s s').
  Proof. 
    Intros s s'; Unfold equal; Case (M.equal s s'); Intuition; Inversion H.
  Save.
  
  Definition subset : t -> t -> bool := 
    [s,s']if (M.subset s s') then [_]true else [_]false.

  Lemma subset_1 : (s,s':t)(Subset s s') -> (subset s s')=true.
  Proof. 
    Intros; Unfold subset; Case M.subset; Intuition.
  Save.    
 
  Lemma subset_2 : (s,s':t)(subset s s')=true -> (Subset s s').
  Proof. 
    Intros s s'; Unfold subset; Case (M.subset s s'); Intuition; Inversion H.
  Save.

  Definition choose : t -> (option elt) :=
    [s:t]Cases (M.choose s) of (inleft (exist x _)) => (Some ? x)
                             | (inright _) => (None ?) end.

  Lemma choose_1 : (s:t)(x:elt) (choose s)=(Some ? x) -> (In x s).
  Proof.
    Intros s x; Unfold choose; Case (M.choose s).
    Destruct s0; Intros; Injection H; Intros; Subst; Auto.
    Intros; Discriminate H.
  Save.

  Lemma choose_2 : (s:t)(choose s)=(None ?) -> (Empty s).
  Proof.
    Intro s; Unfold choose; Case (M.choose s); Auto.
    Destruct s0; Intros; Discriminate H.
  Save.

  Definition elements : t -> (list elt) := [s] let (l,_) = (M.elements s) in l. 
 
  Lemma elements_1: (s:t)(x:elt)(In x s) -> (InList E.eq x (elements s)).
  Proof. 
    Intros; Unfold elements; Case (M.elements s); Ground.
  Save.

  Lemma elements_2: (s:t)(x:elt)(InList E.eq x (elements s)) -> (In x s).
  Proof. 
    Intros s x; Unfold elements; Case (M.elements s); Ground.
  Save.

  Lemma elements_3: (s:t)(sort E.lt (elements s)).  
  Proof. 
    Intros; Unfold elements; Case (M.elements s); Ground.
  Save.

  Definition min_elt : t -> (option elt) :=
    [s:t]Cases (M.min_elt s) of (inleft (exist x _)) => (Some ? x)
                             | (inright _) => (None ?) end.

  Lemma min_elt_1: (s:t)(x:elt)(min_elt s) = (Some ? x) -> (In x s). 
  Proof.
    Intros s x; Unfold min_elt; Case (M.min_elt s).
    Destruct s0; Intros; Injection H; Intros; Subst; Intuition.
    Intros; Discriminate H.
  Save. 

  Lemma min_elt_2: (s:t)(x,y:elt)(min_elt s) = (Some ? x) -> (In y s) -> ~(E.lt y x). 
  Proof.
    Intros s x y; Unfold min_elt; Case (M.min_elt s).
    Unfold For_all; Destruct s0; Intros; Injection H; Intros; Subst; Ground.
    Intros; Discriminate H.
  Save. 

  Lemma min_elt_3 : (s:t)(min_elt s) = (None ?) -> (Empty s).
  Proof.
    Intros s; Unfold min_elt; Case (M.min_elt s); Auto.
    Destruct s0; Intros; Discriminate H.
  Save. 

  Definition max_elt : t -> (option elt) :=
    [s:t]Cases (M.max_elt s) of (inleft (exist x _)) => (Some ? x)
                             | (inright _) => (None ?) end.

  Lemma max_elt_1: (s:t)(x:elt)(max_elt s) = (Some ? x) -> (In x s). 
  Proof.
    Intros s x; Unfold max_elt; Case (M.max_elt s).
    Destruct s0; Intros; Injection H; Intros; Subst; Intuition.
    Intros; Discriminate H.
  Save. 

  Lemma max_elt_2: (s:t)(x,y:elt)(max_elt s) = (Some ? x) -> (In y s) -> ~(E.lt x y). 
  Proof.
    Intros s x y; Unfold max_elt; Case (M.max_elt s).
    Unfold For_all; Destruct s0; Intros; Injection H; Intros; Subst; Ground.
    Intros; Discriminate H.
  Save. 

  Lemma max_elt_3 : (s:t)(max_elt s) = (None ?) -> (Empty s).
  Proof.
    Intros s; Unfold max_elt; Case (M.max_elt s); Auto.
    Destruct s0; Intros; Discriminate H.
  Save. 

  Definition add : elt -> t -> t := 
    [x:elt][s:t]let (s',_) = (M.add x s) in s'.

  Lemma add_1 : (s:t)(x:elt)(In x (add x s)).
  Proof.
    Intros; Unfold add; Case (M.add x s); Unfold Add; Ground.
  Save.

  Lemma add_2 : (s:t)(x,y:elt)(In y s) -> (In y (add x s)).
  Proof.
    Intros; Unfold add; Case (M.add x s); Unfold Add; Ground.
  Save.

  Lemma add_3 : (s:t)(x,y:elt)~(E.eq x y) -> (In y (add x s)) -> (In y s).
  Proof.
    Intros s x y; Unfold add; Case (M.add x s); Unfold Add; Ground.
    Generalize (a y); Intuition; Absurd (E.eq x y); Auto.
  Save.

  Definition remove : elt -> t -> t := 
    [x:elt][s:t]let (s',_) = (M.remove x s) in s'.

  Lemma remove_1 : (s:t)(x:elt)~(In x (remove x s)).
  Proof.
    Intros; Unfold remove; Case (M.remove x s); Ground.
  Save.

  Lemma remove_2 : (s:t)(x,y:elt)
	~(E.eq x y) ->(In y s) -> (In y (remove x s)).
  Proof.
    Intros; Unfold remove; Case (M.remove x s); Ground.
  Save.

  Lemma remove_3 : (s:t)(x,y:elt)(In y (remove x s)) -> (In y s).
  Proof.
    Intros s x y; Unfold remove; Case (M.remove x s); Ground.
  Save.
  
  Definition singleton : elt -> t := [x]let (s,_) = (M.singleton x) in s. 
 
  Lemma singleton_1 : (x,y:elt)(In y (singleton x)) -> (E.eq x y). 
  Proof.
    Intros x y; Unfold singleton; Case (M.singleton x); Ground.
  Save.

  Lemma singleton_2: (x,y:elt)(E.eq x y) -> (In y (singleton x)). 
  Proof.
    Intros x y; Unfold singleton; Case (M.singleton x); Ground.
  Save.
  
  Definition union : t -> t -> t := 
	[s,s']let (s'',_) = (M.union s s') in s''.
 
  Lemma union_1: (s,s':t)(x:elt)(In x (union s s')) -> (In x s)\/(In x s').
  Proof. 
    Intros s s' x; Unfold union; Case (M.union s s'); Ground.
  Save.

  Lemma union_2: (s,s':t)(x:elt)(In x s) -> (In x (union s s')). 
  Proof. 
    Intros s s' x; Unfold union; Case (M.union s s'); Ground.
  Save.

  Lemma union_3: (s,s':t)(x:elt)(In x s') ->  (In x (union s s')).
  Proof. 
    Intros s s' x; Unfold union; Case (M.union s s'); Ground.
  Save.

  Definition inter : t -> t -> t := 
	[s,s']let (s'',_) = (M.inter s s') in s''.
 
  Lemma inter_1: (s,s':t)(x:elt)(In x (inter s s')) -> (In x s).
  Proof. 
    Intros s s' x; Unfold inter; Case (M.inter s s'); Ground.
  Save.

  Lemma inter_2: (s,s':t)(x:elt)(In x (inter s s')) -> (In x s').
  Proof. 
    Intros s s' x; Unfold inter; Case (M.inter s s'); Ground.
  Save.

  Lemma inter_3: (s,s':t)(x:elt)(In x s) -> (In x s') -> (In x (inter s s')).
  Proof. 
    Intros s s' x; Unfold inter; Case (M.inter s s'); Ground.
  Save.

  Definition diff : t -> t -> t := 
	[s,s']let (s'',_) = (M.diff s s') in s''.
 
  Lemma diff_1: (s,s':t)(x:elt)(In x (diff s s')) -> (In x s).
  Proof. 
    Intros s s' x; Unfold diff; Case (M.diff s s'); Ground.
  Save.

  Lemma diff_2: (s,s':t)(x:elt)(In x (diff s s')) -> ~(In x s').
  Proof. 
    Intros s s' x; Unfold diff; Case (M.diff s s'); Ground.
  Save.

  Lemma diff_3: (s,s':t)(x:elt)(In x s) -> ~(In x s') -> (In x (diff s s')).
  Proof. 
    Intros s s' x; Unfold diff; Case (M.diff s s'); Ground.
  Save.

  Definition cardinal : t -> nat := [s]let (f,_)= (M.cardinal s) in f.

  Lemma cardinal_1 : 
    (s:t)(EX l:(list elt) | 
             (Unique E.eq l) /\
             ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
             (cardinal s)=(length l)).
  Proof.
    Intros; Unfold cardinal; Case (M.cardinal s); Ground.
  Qed.

  Definition fold : (B:Set)(elt->B->B)->t->B->B :=  
       [B,f,i,s]let (fold,_)= (M.fold f i s) in fold.

  Lemma fold_1: 
   (s:t)(A:Set)(i:A)(f:elt->A->A)
   (EX l:(list elt) | 
       (Unique E.eq l) /\ 
       ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
       (fold f s i)=(fold_right f i l)).
  Proof.
    Intros; Unfold fold; Case (M.fold f s i); Ground.
  Save.  

  Definition f_dec : 
    (f: elt -> bool)(x:elt){ (f x)=true } + { (f x)<>true }.
  Proof.
    Intros; Case (f x); Auto with bool.
  Defined. 

  Lemma compat_P_aux : 
     (f:elt -> bool)(compat_bool E.eq f) -> (compat_P E.eq [x](f x)=true).
  Proof.
     Unfold compat_bool compat_P; Intros; Rewrite <- H1; Ground.
  Qed.

  Hints Resolve compat_P_aux.
    
  Definition filter : (elt -> bool) -> t -> t := 
     [f,s]let (s',_) = (!M.filter [x](f x)=true (f_dec f) s) in s'.

  Lemma filter_1: (s:t)(x:elt)(f:elt->bool)(compat_bool E.eq f) -> 
     (In x (filter f s)) -> (In x s).
  Proof.
    Intros s x f; Unfold filter; Case M.filter; Intuition.
    Generalize (i (compat_P_aux H)); Ground.
  Save.

  Lemma filter_2: 
    (s:t)(x:elt)(f:elt->bool)(compat_bool E.eq f) ->(In x (filter f s)) -> (f x)=true. 
  Proof.
    Intros s x f; Unfold filter; Case M.filter; Intuition.
    Generalize (i (compat_P_aux H)); Ground.
  Save.

  Lemma filter_3: 
    (s:t)(x:elt)(f:elt->bool)(compat_bool E.eq f) -> 
        (In x s) -> (f x)=true -> (In x (filter f s)).     
  Proof.
    Intros s x f; Unfold filter; Case M.filter; Intuition.
    Generalize (i (compat_P_aux H)); Ground.
  Save.

  Definition for_all: (elt -> bool) -> t -> bool := 
     [f,s]if (!M.for_all [x](f x)=true (f_dec f) s) then [_]true else [_]false. 

  Lemma for_all_1: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> 
       (For_all [x](f x)=true s) -> (for_all f s)=true.
  Proof. 
    Intros s f; Unfold for_all; Case M.for_all; Intuition; Elim n; Auto.
  Qed.
 
  Lemma for_all_2: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) ->(for_all f s)=true -> (For_all [x](f x)=true s).
  Proof. 
    Intros s f; Unfold for_all; Case M.for_all; Intuition; Inversion H0.
  Qed.
  
  Definition exists: (elt -> bool) -> t -> bool := 
     [f,s]if (!M.exists [x](f x)=true (f_dec f) s) then [_]true else [_]false. 

  Lemma exists_1: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) ->
       (Exists [x](f x)=true s) -> (exists f s)=true.
  Proof. 
    Intros s f; Unfold exists; Case M.exists; Intuition; Elim n; Auto.
  Qed.
 
  Lemma exists_2: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> 
       (exists f s)=true -> (Exists [x](f x)=true s).
  Proof. 
    Intros s f; Unfold exists; Case M.exists; Intuition; Inversion H0.
  Qed.
     
  Definition partition : (elt -> bool) -> t -> t*t := 
    [f,s]let (p,_) = (!M.partition [x](f x)=true (f_dec f) s) in p.
  
  Lemma partition_1: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> (Equal (fst ? ? (partition f s)) (filter f s)).
  Proof.
    Intros s f; Unfold partition; Case M.partition. 
    Intro p; Case p; Clear p; Intros s1 s2 H C. 
    Generalize (H (compat_P_aux C)); Clear H; Intro H.
    Simpl; Unfold Equal; Intuition.
    Apply filter_3; Ground. 
    Elim (H2 a); Intros. 
    Assert (In a s). 
     EApply filter_1; EAuto.
    Elim H3; Intros; Auto.
    Absurd (f a)=true.
    Exact (H a H6).
    EApply filter_2; EAuto. 
  Qed.    
    
  Lemma partition_2: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> 
    (Equal (snd ? ? (partition f s)) (filter [x](negb (f x)) s)).
  Proof.
    Intros s f; Unfold partition; Case M.partition. 
    Intro p; Case p; Clear p; Intros s1 s2 H C. 
    Generalize (H (compat_P_aux C)); Clear H; Intro H.
    Assert D: (compat_bool E.eq [x](negb (f x))).
    Generalize C; Unfold compat_bool; Intros; Apply (f_equal ?? negb); Auto.
    Simpl; Unfold Equal; Intuition.
    Apply filter_3; Ground.
    Elim (H2 a); Intros. 
    Assert (In a s). 
     EApply filter_1; EAuto.
    Elim H3; Intros; Auto.
    Absurd (f a)=true.
    Intro.
    Generalize (filter_2  D H1). 
    Rewrite H7; Intros H8; Inversion H8.
    Exact (H0 a H6).
  Qed. 


  Module E:=E. 
  Definition elt := elt.
  Definition t := t.

  Definition In := In. 
  Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
  Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
  Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
  Definition Empty := [s](a:elt)~(In a s).
  Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
  Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).

  Definition In_1 := eq_In.

  Definition eq := eq.
  Definition lt := lt.
  Definition eq_refl := eq_refl.
  Definition eq_sym := eq_sym.
  Definition eq_trans := eq_trans.
  Definition lt_trans := lt_trans. 
  Definition lt_not_eq := lt_not_eq.
  Definition compare := compare.

End NodepOfDep.

