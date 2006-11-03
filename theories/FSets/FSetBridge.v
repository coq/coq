(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite sets library *)

(** This module implements bridges (as functors) from dependent
    to/from non-dependent set signature. *)

Require Export FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.
Set Firstorder Depth 2.

(** * From non-dependent signature [S] to dependent signature [Sdep]. *)

Module DepOfNodep (M: S) <: Sdep with Module E := M.E.
  Import M.

  Module ME := OrderedTypeFacts E.
   
  Definition empty : {s : t | Empty s}.
  Proof. 
    exists empty; auto.
  Qed.

  Definition is_empty : forall s : t, {Empty s} + {~ Empty s}.
  Proof. 
    intros; generalize (is_empty_1 (s:=s)) (is_empty_2 (s:=s)).
    case (is_empty s); intuition.
  Qed.


  Definition mem : forall (x : elt) (s : t), {In x s} + {~ In x s}.
  Proof. 
    intros; generalize (mem_1 (s:=s) (x:=x)) (mem_2 (s:=s) (x:=x)).
    case (mem x s); intuition.
  Qed.
 
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq x y \/ In y s.
 
  Definition add : forall (x : elt) (s : t), {s' : t | Add x s s'}.
  Proof.
    intros; exists (add x s); auto.
    unfold Add in |- *; intuition.
    elim (ME.eq_dec x y); auto.
    intros; right. 
    eapply add_3; eauto.
  Qed. 
 
  Definition singleton :
    forall x : elt, {s : t | forall y : elt, In y s <-> E.eq x y}.
  Proof. 
    intros; exists (singleton x); intuition.
  Qed.
 
  Definition remove :
    forall (x : elt) (s : t),
    {s' : t | forall y : elt, In y s' <-> ~ E.eq x y /\ In y s}.
  Proof.
    intros; exists (remove x s); intuition.
    absurd (In x (remove x s)); auto.
    apply In_1 with y; auto. 
    elim (ME.eq_dec x y); intros; auto.
    absurd (In x (remove x s)); auto.
    apply In_1 with y; auto. 
    eauto.
  Qed.

  Definition union :
    forall s s' : t, {s'' : t | forall x : elt, In x s'' <-> In x s \/ In x s'}.
  Proof.
    intros; exists (union s s'); intuition.
  Qed.    

  Definition inter :
    forall s s' : t, {s'' : t | forall x : elt, In x s'' <-> In x s /\ In x s'}.
  Proof. 
    intros; exists (inter s s'); intuition; eauto.
  Qed.

  Definition diff :
    forall s s' : t, {s'' : t | forall x : elt, In x s'' <-> In x s /\ ~ In x s'}.
  Proof. 
    intros; exists (diff s s'); intuition; eauto. 
    absurd (In x s'); eauto. 
  Qed. 
 
  Definition equal : forall s s' : t, {Equal s s'} + {~ Equal s s'}.
  Proof. 
    intros. 
    generalize (equal_1 (s:=s) (s':=s')) (equal_2 (s:=s) (s':=s')).
    case (equal s s'); intuition.
  Qed.

  Definition subset : forall s s' : t, {Subset s s'} + {~Subset s s'}.
  Proof. 
    intros. 
    generalize (subset_1 (s:=s) (s':=s')) (subset_2 (s:=s) (s':=s')).
    case (subset s s'); intuition.
  Qed.   

  Definition elements :
    forall s : t,
    {l : list elt | sort E.lt l /\ (forall x : elt, In x s <-> InA E.eq x l)}.
   Proof.
     intros; exists (elements s); intuition.   
   Defined. 

  Definition fold :
    forall (A : Set) (f : elt -> A -> A) (s : t) (i : A),
    {r : A |   let (l,_) := elements s in 
                  r = fold_left (fun a e => f e a) l i}.
  Proof. 
  intros; exists (fold (A:=A) f s i); exact (fold_1 s i f).
  Qed.

  Definition cardinal :
      forall s : t,
      {r : nat | let (l,_) := elements s in r = length l }.
  Proof.
    intros; exists (cardinal s); exact (cardinal_1 s).
  Qed.    

  Definition fdec (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
    (x : elt) := if Pdec x then true else false. 

  Lemma compat_P_aux :
   forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}),
   compat_P E.eq P -> compat_bool E.eq (fdec Pdec).
  Proof.
    unfold compat_P, compat_bool, fdec in |- *; intros.
    generalize (E.eq_sym H0); case (Pdec x); case (Pdec y); firstorder.
  Qed.

  Hint Resolve compat_P_aux.

  Definition filter :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {s' : t | compat_P E.eq P -> forall x : elt, In x s' <-> In x s /\ P x}.
  Proof.
    intros. 
    exists (filter (fdec Pdec) s).
    intro H; assert (compat_bool E.eq (fdec Pdec)); auto.
    intuition.
    eauto.
    generalize (filter_2 H0 H1).
    unfold fdec in |- *.
    case (Pdec x); intuition.
    inversion H2.
    apply filter_3; auto.
    unfold fdec in |- *; simpl in |- *.
    case (Pdec x); intuition.
  Qed.

  Definition for_all :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {compat_P E.eq P -> For_all P s} + {compat_P E.eq P -> ~ For_all P s}.
  Proof. 
    intros. 
    generalize (for_all_1 (s:=s) (f:=fdec Pdec))
     (for_all_2 (s:=s) (f:=fdec Pdec)).
    case (for_all (fdec Pdec) s); unfold For_all in |- *; [ left | right ];
     intros.
    assert (compat_bool E.eq (fdec Pdec)); auto.
    generalize (H0 H3 (refl_equal _) _ H2).
    unfold fdec in |- *. 
    case (Pdec x); intuition.
    inversion H4.
    intuition.    
    absurd (false = true); [ auto with bool | apply H; auto ].
    intro.
    unfold fdec in |- *. 
    case (Pdec x); intuition.
  Qed.

  Definition exists_ :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {compat_P E.eq P -> Exists P s} + {compat_P E.eq P -> ~ Exists P s}.
  Proof. 
    intros. 
    generalize (exists_1 (s:=s) (f:=fdec Pdec))
     (exists_2 (s:=s) (f:=fdec Pdec)).
    case (exists_ (fdec Pdec) s); unfold Exists in |- *; [ left | right ];
     intros.
    elim H0; auto; intros.
    exists x; intuition.
    generalize H4.
    unfold fdec in |- *. 
    case (Pdec x); intuition.
    inversion H2.
    intuition. 
    elim H2; intros.    
    absurd (false = true); [ auto with bool | apply H; auto ].
    exists x; intuition.
    unfold fdec in |- *. 
    case (Pdec x); intuition.
  Qed.

  Definition partition :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {partition : t * t |
    let (s1, s2) := partition in
    compat_P E.eq P ->
    For_all P s1 /\
    For_all (fun x => ~ P x) s2 /\
    (forall x : elt, In x s <-> In x s1 \/ In x s2)}.
  Proof.
    intros.
    exists (partition (fdec Pdec) s).
    generalize (partition_1 s (f:=fdec Pdec)) (partition_2 s (f:=fdec Pdec)).
    case (partition (fdec Pdec) s).
    intros s1 s2; simpl in |- *.
    intros; assert (compat_bool E.eq (fdec Pdec)); auto.
    intros; assert (compat_bool E.eq (fun x => negb (fdec Pdec x))).
    generalize H2; unfold compat_bool in |- *; intuition;
     apply (f_equal negb); auto.
    intuition.
    generalize H4; unfold For_all, Equal in |- *; intuition.
    elim (H0 x); intros.
    assert (fdec Pdec x = true).
     eauto.      
    generalize H8; unfold fdec in |- *; case (Pdec x); intuition.
    inversion H9.
    generalize H; unfold For_all, Equal in |- *; intuition.
    elim (H0 x); intros.
    cut ((fun x => negb (fdec Pdec x)) x = true). 
    unfold fdec in |- *; case (Pdec x); intuition.
      change ((fun x => negb (fdec Pdec x)) x = true) in |- *.
      apply (filter_2 (s:=s) (x:=x)); auto.
    set (b := fdec Pdec x) in *; generalize (refl_equal b);
     pattern b at -1 in |- *; case b; unfold b in |- *; 
     [ left | right ].
    elim (H4 x); intros _ B; apply B; auto.
    elim (H x); intros _ B; apply B; auto.
    apply filter_3; auto.
    rewrite H5; auto.
    eapply (filter_1 (s:=s) (x:=x) H2); elim (H4 x); intros B _; apply B;
     auto.
    eapply (filter_1 (s:=s) (x:=x) H3); elim (H x); intros B _; apply B; auto.
  Qed. 

  Definition choose : forall s : t, {x : elt | In x s} + {Empty s}.
  Proof.  
    intros.
    generalize (choose_1 (s:=s)) (choose_2 (s:=s)).
    case (choose s); [ left | right ]; auto.
    exists e; auto.    
  Qed.

  Definition min_elt :
    forall s : t,
    {x : elt | In x s /\ For_all (fun y => ~ E.lt y x) s} + {Empty s}.
  Proof. 
    intros;
     generalize (min_elt_1 (s:=s)) (min_elt_2 (s:=s)) (min_elt_3 (s:=s)).
    case (min_elt s); [ left | right ]; auto.    
    exists e; unfold For_all in |- *; eauto.
  Qed. 

  Definition max_elt :
    forall s : t,
    {x : elt | In x s /\ For_all (fun y => ~ E.lt x y) s} + {Empty s}.
  Proof. 
    intros;
     generalize (max_elt_1 (s:=s)) (max_elt_2 (s:=s)) (max_elt_3 (s:=s)).
    case (max_elt s); [ left | right ]; auto.    
    exists e; unfold For_all in |- *; eauto.
  Qed. 

  Module E := E. 

  Definition elt := elt.
  Definition t := t.

  Definition In := In. 
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.
  
  Definition eq_In := In_1.

  Definition eq := Equal.
  Definition lt := lt.
  Definition eq_refl := eq_refl.
  Definition eq_sym := eq_sym.
  Definition eq_trans := eq_trans.
  Definition lt_trans := lt_trans. 
  Definition lt_not_eq := lt_not_eq.
  Definition compare := compare.

End DepOfNodep.


(** * From dependent signature [Sdep] to non-dependent signature [S]. *)

Module NodepOfDep (M: Sdep) <: S with Module E := M.E.
  Import M.

  Module ME := OrderedTypeFacts E.

  Definition empty : t := let (s, _) := empty in s.

  Lemma empty_1 : Empty empty.
  Proof.
    unfold empty in |- *; case M.empty; auto.
  Qed.

  Definition is_empty (s : t) : bool :=
    if is_empty s then true else false.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros; unfold is_empty in |- *; case (M.is_empty s); auto.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    intro s; unfold is_empty in |- *; case (M.is_empty s); auto.
    intros; discriminate H.
  Qed.

  Definition mem (x : elt) (s : t) : bool :=
    if mem x s then true else false.

  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof.
    intros; unfold mem in |- *; case (M.mem x s); auto.
  Qed.
   
  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
    intros s x; unfold mem in |- *; case (M.mem x s); auto.
    intros; discriminate H.
  Qed.

  Definition equal (s s' : t) : bool :=
    if equal s s' then true else false.

  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof. 
    intros; unfold equal in |- *; case M.equal; intuition.
  Qed.    
 
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof. 
    intros s s'; unfold equal in |- *; case (M.equal s s'); intuition;
     inversion H.
  Qed.
  
  Definition subset (s s' : t) : bool :=
    if subset s s' then true else false.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof. 
    intros; unfold subset in |- *; case M.subset; intuition.
  Qed.    
 
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof. 
    intros s s'; unfold subset in |- *; case (M.subset s s'); intuition;
     inversion H.
  Qed.

  Definition choose (s : t) : option elt :=
    match choose s with
    | inleft (exist x _) => Some x
    | inright _ => None
    end.

  Lemma choose_1 : forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
    intros s x; unfold choose in |- *; case (M.choose s).
    simple destruct s0; intros; injection H; intros; subst; auto.
    intros; discriminate H.
  Qed.

  Lemma choose_2 : forall s : t, choose s = None -> Empty s.
  Proof.
    intro s; unfold choose in |- *; case (M.choose s); auto.
    simple destruct s0; intros; discriminate H.
  Qed.

  Definition elements (s : t) : list elt := let (l, _) := elements s in l. 
 
  Lemma elements_1 : forall (s : t) (x : elt), In x s -> InA E.eq x (elements s).
  Proof. 
    intros; unfold elements in |- *; case (M.elements s); firstorder.
  Qed.

  Lemma elements_2 : forall (s : t) (x : elt), InA E.eq x (elements s) -> In x s.
  Proof. 
    intros s x; unfold elements in |- *; case (M.elements s); firstorder.
  Qed.

  Lemma elements_3 : forall s : t, sort E.lt (elements s).  
  Proof. 
    intros; unfold elements in |- *; case (M.elements s); firstorder.
  Qed.

  Definition min_elt (s : t) : option elt :=
    match min_elt s with
    | inleft (exist x _) => Some x
    | inright _ => None
    end.

  Lemma min_elt_1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s. 
  Proof.
    intros s x; unfold min_elt in |- *; case (M.min_elt s).
    simple destruct s0; intros; injection H; intros; subst; intuition.
    intros; discriminate H.
  Qed. 

  Lemma min_elt_2 :
   forall (s : t) (x y : elt), min_elt s = Some x -> In y s -> ~ E.lt y x. 
  Proof.
    intros s x y; unfold min_elt in |- *; case (M.min_elt s).
    unfold For_all in |- *; simple destruct s0; intros; injection H; intros;
     subst; firstorder.
    intros; discriminate H.
  Qed. 

  Lemma min_elt_3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
    intros s; unfold min_elt in |- *; case (M.min_elt s); auto.
    simple destruct s0; intros; discriminate H.
  Qed. 

  Definition max_elt (s : t) : option elt :=
    match max_elt s with
    | inleft (exist x _) => Some x
    | inright _ => None
    end.

  Lemma max_elt_1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s. 
  Proof.
    intros s x; unfold max_elt in |- *; case (M.max_elt s).
    simple destruct s0; intros; injection H; intros; subst; intuition.
    intros; discriminate H.
  Qed. 

  Lemma max_elt_2 :
   forall (s : t) (x y : elt), max_elt s = Some x -> In y s -> ~ E.lt x y. 
  Proof.
    intros s x y; unfold max_elt in |- *; case (M.max_elt s).
    unfold For_all in |- *; simple destruct s0; intros; injection H; intros;
     subst; firstorder.
    intros; discriminate H.
  Qed. 

  Lemma max_elt_3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
    intros s; unfold max_elt in |- *; case (M.max_elt s); auto.
    simple destruct s0; intros; discriminate H.
  Qed. 

  Definition add (x : elt) (s : t) : t := let (s', _) := add x s in s'.

  Lemma add_1 : forall (s : t) (x y : elt), E.eq x y -> In y (add x s).
  Proof.
    intros; unfold add in |- *; case (M.add x s); unfold Add in |- *;
     firstorder.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    intros; unfold add in |- *; case (M.add x s); unfold Add in |- *;
     firstorder.
  Qed.

  Lemma add_3 :
   forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
    intros s x y; unfold add in |- *; case (M.add x s); unfold Add in |- *;
     firstorder.
  Qed.

  Definition remove (x : elt) (s : t) : t := let (s', _) := remove x s in s'.

  Lemma remove_1 : forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s).
  Proof.
    intros; unfold remove in |- *; case (M.remove x s); firstorder.
  Qed.

  Lemma remove_2 :
   forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s).
  Proof.
    intros; unfold remove in |- *; case (M.remove x s); firstorder.
  Qed.

  Lemma remove_3 : forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    intros s x y; unfold remove in |- *; case (M.remove x s); firstorder.
  Qed.
  
  Definition singleton (x : elt) : t := let (s, _) := singleton x in s. 
 
  Lemma singleton_1 : forall x y : elt, In y (singleton x) -> E.eq x y. 
  Proof.
    intros x y; unfold singleton in |- *; case (M.singleton x); firstorder.
  Qed.

  Lemma singleton_2 : forall x y : elt, E.eq x y -> In y (singleton x). 
  Proof.
    intros x y; unfold singleton in |- *; case (M.singleton x); firstorder.
  Qed.
  
  Definition union (s s' : t) : t := let (s'', _) := union s s' in s''.
 
  Lemma union_1 :
   forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
  Proof. 
    intros s s' x; unfold union in |- *; case (M.union s s'); firstorder.
  Qed.

  Lemma union_2 : forall (s s' : t) (x : elt), In x s -> In x (union s s'). 
  Proof. 
    intros s s' x; unfold union in |- *; case (M.union s s'); firstorder.
  Qed.

  Lemma union_3 : forall (s s' : t) (x : elt), In x s' -> In x (union s s').
  Proof. 
    intros s s' x; unfold union in |- *; case (M.union s s'); firstorder.
  Qed.

  Definition inter (s s' : t) : t := let (s'', _) := inter s s' in s''.
 
  Lemma inter_1 : forall (s s' : t) (x : elt), In x (inter s s') -> In x s.
  Proof. 
    intros s s' x; unfold inter in |- *; case (M.inter s s'); firstorder.
  Qed.

  Lemma inter_2 : forall (s s' : t) (x : elt), In x (inter s s') -> In x s'.
  Proof. 
    intros s s' x; unfold inter in |- *; case (M.inter s s'); firstorder.
  Qed.

  Lemma inter_3 :
   forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s').
  Proof. 
    intros s s' x; unfold inter in |- *; case (M.inter s s'); firstorder.
  Qed.

  Definition diff (s s' : t) : t := let (s'', _) := diff s s' in s''.
 
  Lemma diff_1 : forall (s s' : t) (x : elt), In x (diff s s') -> In x s.
  Proof. 
    intros s s' x; unfold diff in |- *; case (M.diff s s'); firstorder.
  Qed.

  Lemma diff_2 : forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'.
  Proof. 
    intros s s' x; unfold diff in |- *; case (M.diff s s'); firstorder.
  Qed.

  Lemma diff_3 :
   forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s').
  Proof. 
    intros s s' x; unfold diff in |- *; case (M.diff s s'); firstorder.
  Qed.

  Definition cardinal (s : t) : nat := let (f, _) := cardinal s in f.

  Lemma cardinal_1 : forall s, cardinal s = length (elements s).
  Proof.
    intros; unfold cardinal in |- *; case (M.cardinal s); unfold elements in *; 
    destruct (M.elements s); auto.
  Qed.

  Definition fold (B : Set) (f : elt -> B -> B) (i : t) 
    (s : B) : B := let (fold, _) := fold f i s in fold.

  Lemma fold_1 :
   forall (s : t) (A : Set) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof.
    intros; unfold fold in |- *; case (M.fold f s i); unfold elements in *; 
    destruct (M.elements s); auto.
  Qed.  

  Definition f_dec :
    forall (f : elt -> bool) (x : elt), {f x = true} + {f x <> true}.
  Proof.
    intros; case (f x); auto with bool.
  Defined. 

  Lemma compat_P_aux :
   forall f : elt -> bool,
   compat_bool E.eq f -> compat_P E.eq (fun x => f x = true).
  Proof.
     unfold compat_bool, compat_P in |- *; intros; rewrite <- H1; firstorder.
  Qed.

  Hint Resolve compat_P_aux.
    
  Definition filter (f : elt -> bool) (s : t) : t :=
    let (s', _) := filter (P:=fun x => f x = true) (f_dec f) s in s'.

  Lemma filter_1 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof.
    intros s x f; unfold filter in |- *; case M.filter; intuition.
    generalize (i (compat_P_aux H)); firstorder.
  Qed.

  Lemma filter_2 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool E.eq f -> In x (filter f s) -> f x = true. 
  Proof.
    intros s x f; unfold filter in |- *; case M.filter; intuition.
    generalize (i (compat_P_aux H)); firstorder.
  Qed.

  Lemma filter_3 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).     
  Proof.
    intros s x f; unfold filter in |- *; case M.filter; intuition.
    generalize (i (compat_P_aux H)); firstorder.
  Qed.

  Definition for_all (f : elt -> bool) (s : t) : bool :=
    if for_all (P:=fun x => f x = true) (f_dec f) s
    then true
    else false. 

  Lemma for_all_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f ->
   For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. 
    intros s f; unfold for_all in |- *; case M.for_all; intuition; elim n;
     auto.
  Qed.
 
  Lemma for_all_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f ->
   for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. 
    intros s f; unfold for_all in |- *; case M.for_all; intuition;
     inversion H0.
  Qed.
  
  Definition exists_ (f : elt -> bool) (s : t) : bool :=
    if exists_ (P:=fun x => f x = true) (f_dec f) s
    then true
    else false. 

  Lemma exists_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof. 
    intros s f; unfold exists_ in |- *; case M.exists_; intuition; elim n;
     auto.
  Qed.
 
  Lemma exists_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. 
    intros s f; unfold exists_ in |- *; case M.exists_; intuition;
     inversion H0.
  Qed.
     
  Definition partition (f : elt -> bool) (s : t) : 
    t * t :=
    let (p, _) := partition (P:=fun x => f x = true) (f_dec f) s in p.
  
  Lemma partition_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros s f; unfold partition in |- *; case M.partition. 
    intro p; case p; clear p; intros s1 s2 H C. 
    generalize (H (compat_P_aux C)); clear H; intro H.
    simpl in |- *; unfold Equal in |- *; intuition.
    apply filter_3; firstorder. 
    elim (H2 a); intros. 
    assert (In a s). 
     eapply filter_1; eauto.
    elim H3; intros; auto.
    absurd (f a = true).
    exact (H a H6).
    eapply filter_2; eauto. 
  Qed.    
    
  Lemma partition_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
    intros s f; unfold partition in |- *; case M.partition. 
    intro p; case p; clear p; intros s1 s2 H C. 
    generalize (H (compat_P_aux C)); clear H; intro H.
    assert (D : compat_bool E.eq (fun x => negb (f x))).
    generalize C; unfold compat_bool in |- *; intros; apply (f_equal negb);
     auto.
    simpl in |- *; unfold Equal in |- *; intuition.
    apply filter_3; firstorder.
    elim (H2 a); intros. 
    assert (In a s). 
     eapply filter_1; eauto.
    elim H3; intros; auto.
    absurd (f a = true).
    intro.
    generalize (filter_2 D H1). 
    rewrite H7; intros H8; inversion H8.
    exact (H0 a H6).
  Qed. 


  Module E := E. 
  Definition elt := elt.
  Definition t := t.

  Definition In := In. 
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq y x \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.

  Definition In_1 := eq_In.

  Definition eq := Equal.
  Definition lt := lt.
  Definition eq_refl := eq_refl.
  Definition eq_sym := eq_sym.
  Definition eq_trans := eq_trans.
  Definition lt_trans := lt_trans. 
  Definition lt_not_eq := lt_not_eq.
  Definition compare := compare.

End NodepOfDep.
