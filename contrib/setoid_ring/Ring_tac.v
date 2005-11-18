Set Implicit Arguments.
Require Import Setoid.
Require Import BinList.
Require Import BinPos.
Require Import Pol.
Declare ML Module "newring".

(* Some Tactics *)

Ltac compute_assertion id t :=
  let t' := eval compute in t in
  (assert (id : t = t'); [exact_no_check (refl_equal t')|idtac]).

Ltac compute_assertion' id  id' t :=
  let t' := eval compute in t in
  (pose (id' := t');
   assert (id : t = id');
   [exact_no_check (refl_equal id')|idtac]).

Ltac compute_replace' id t :=
  let t' := eval compute in t in
  (replace t with t' in id; [idtac|exact_no_check (refl_equal t')]).

Ltac bin_list_fold_right fcons fnil l :=
  match l with
  | (cons ?x ?tl) => fcons x ltac:(bin_list_fold_right fcons fnil tl)
  | (nil _) => fnil
  end.

Ltac bin_list_fold_left fcons fnil l :=
  match l with
  | (cons ?x ?tl) => bin_list_fold_left fcons ltac:(fcons x fnil) tl
  | (nil _) => fnil
  end.

Ltac bin_list_iter f l :=
  match l with
  | (cons ?x ?tl) => f x; bin_list_iter f tl
  | (nil _) => idtac
  end.
 
(** A tactic that reverses a list *)
Ltac Trev R l :=  
  let rec rev_append rev l :=
   match l with
   | (nil _) => constr:(rev)
   | (cons ?h ?t) => let rev := constr:(cons h rev) in rev_append rev t 
   end in
 rev_append (nil R) l.

(* to avoid conflicts with Coq booleans*)
Definition NotConstant := false.
 		       
Ltac IN a l :=
 match l with
 | (cons a ?l) => true
 | (cons _ ?l) => IN a l
 | (nil _) => false
 end.

Ltac AddFv a l :=
 match (IN a l) with
 | true => l
 | _ => constr:(cons a l)
 end.

Ltac Find_at a l :=
 match l with
 | (nil _) => fail 1 "ring anomaly"
 | (cons a _) => constr:1%positive
 | (cons _ ?l) => let p := Find_at a l in eval compute in (Psucc p)
 end.
		      
Ltac FV Cst add mul sub opp t fv :=
 let rec TFV t fv :=
  match Cst t with
  | NotConstant =>
      match t with
      | (add ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (mul ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (sub ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (opp ?t1) => TFV t1 fv
      | _ => AddFv t fv
      end
  | _ => fv
  end 
 in TFV t fv.

 (* syntaxification *)
 Ltac mkPolexpr C Cst radd rmul rsub ropp t fv := 
 let rec mkP t :=
    match Cst t with
    | NotConstant =>
        match t with 
        | (radd ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEadd e1 e2)
        | (rmul ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEmul e1 e2)
        | (rsub ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEsub e1 e2)
        | (ropp ?t1) =>
          let e1 := mkP t1 in constr:(PEopp e1)
        | _ =>
          let p := Find_at t fv in constr:(PEX C p)
        end
    | ?c => constr:(PEc c)
    end
 in mkP t.

(* ring tactics *)
Ltac Make_ring_rewrite_step lemma pe:=
  let npe := fresh "npe" in
  let H := fresh "eq_npe" in
  let Heq := fresh "ring_thm" in
  let npe_spec :=
    match type of (lemma pe) with
      forall (npe:_), ?npe_spec = npe -> _ => npe_spec
    | _ => fail 1 "cannot find norm expression"
    end in
  (compute_assertion' H  npe npe_spec;
   assert (Heq:=lemma _ _ H); clear H;
   protect_fv in Heq;
   (rewrite Heq; clear Heq npe) || clear npe).


Ltac Make_ring_rw_list Cst_tac lemma req rl :=
  match type of lemma with
    forall (l:list ?R) (pe:PExpr ?C) (npe:Pol ?C),
    _ = npe ->
    req (PEeval ?rO ?add ?mul ?sub ?opp ?phi l pe) _ =>
  let mkFV := FV Cst_tac add mul sub opp in
  let mkPol := mkPolexpr C Cst_tac add mul sub opp in
  (* build the atom list *)
  let rfv := bin_list_fold_left mkFV (nil R) rl in
  let fv := Trev R rfv in
  (* rewrite *)
  bin_list_iter
    ltac:(fun r =>
      let pe := mkPol r fv in
      Make_ring_rewrite_step (lemma fv) pe)
    rl
  | _ => fail 1 "bad lemma"
  end.

Ltac Make_ring_rw Cst_tac lemma req r :=
  Make_ring_rw_list Cst_tac lemma req (cons r (nil _)).

 (* Building the generic tactic *)

 Ltac Make_ring_tac Cst_tac lemma1 lemma2 req :=
  match type of lemma2 with
    forall (l:list ?R) (pe:PExpr ?C) (npe:Pol ?C),
    _ = npe ->
    req (PEeval ?rO ?add ?mul ?sub ?opp ?phi l pe) _ =>
  match goal with
  | |- req ?r1 ?r2 =>
    let mkFV := FV Cst_tac add mul sub opp in
    let mkPol := mkPolexpr C Cst_tac add mul sub opp in
    let rfv := mkFV (add r1 r2) (nil R) in
    let fv := Trev R rfv in
    let pe1 := mkPol r1 fv in
    let pe2 := mkPol r2 fv in
    ((apply (lemma1 fv pe1 pe2);
      compute;
      exact (refl_equal true)) ||
     (Make_ring_rewrite_step (lemma2 fv) pe1;
      Make_ring_rewrite_step (lemma2 fv) pe2))
  | _ => fail 1 "goal is not an equality from a declared ring"
  end
  end.


(* coefs belong to the same type as the target ring (concrete ring) *)
Definition ring_id_correct
  R rO rI radd rmul rsub ropp req rSet req_th ARth reqb reqb_ok :=
  @ring_correct R rO rI radd rmul rsub ropp req rSet req_th ARth
                R rO rI radd rmul rsub ropp reqb
               (@IDphi R)
               (@IDmorph R rO rI radd rmul rsub ropp req rSet reqb reqb_ok).

Definition ring_rw_id_correct
  R rO rI radd rmul rsub ropp req rSet req_th ARth reqb reqb_ok :=
  @Pphi_dev_ok  R rO rI radd rmul rsub ropp req rSet req_th ARth
                R rO rI radd rmul rsub ropp reqb
               (@IDphi R)
               (@IDmorph R rO rI radd rmul rsub ropp req rSet reqb reqb_ok).

Definition ring_rw_id_correct'
  R rO rI radd rmul rsub ropp req rSet req_th ARth reqb reqb_ok :=
  @Pphi_dev_ok'  R rO rI radd rmul rsub ropp req rSet req_th ARth
                 R rO rI radd rmul rsub ropp reqb
                (@IDphi R)
                (@IDmorph R rO rI radd rmul rsub ropp req rSet reqb reqb_ok).

Definition ring_id_eq_correct R rO rI radd rmul rsub ropp ARth reqb reqb_ok :=
 @ring_id_correct R rO rI radd rmul rsub ropp (@eq R)
    (Eqsth R) (Eq_ext _ _ _) ARth reqb reqb_ok.

Definition ring_rw_id_eq_correct
   R rO rI radd rmul rsub ropp ARth reqb reqb_ok :=
 @ring_rw_id_correct R rO rI radd rmul rsub ropp (@eq R)
    (Eqsth R) (Eq_ext _ _ _) ARth reqb reqb_ok.

Definition ring_rw_id_eq_correct'
   R rO rI radd rmul rsub ropp ARth reqb reqb_ok :=
 @ring_rw_id_correct' R rO rI radd rmul rsub ropp (@eq R)
    (Eqsth R) (Eq_ext _ _ _) ARth reqb reqb_ok.

(*
Require Import ZArith.
Require Import Setoid.
Require Import Ring_tac.
Import BinList.
Import Ring_th.
Open Scope Z_scope.

Add New Ring Zr : (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth)
  Computational Zeqb_ok
  Constant Zcst.

Goal forall a b, (a+b*2)*(a+b*2)=1.
intros.
 setoid ring ((a + b * 2) * (a + b * 2)).

  Make_ring_rw_list Zcst
    (ring_rw_id_correct' (Eqsth Z) (Eq_ext _ _ _)
      (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok)
    (eq (A:=Z))
   (cons ((a+b)*(a+b)) (nil _)).


Goal forall a b, (a+b)*(a+b)=1.
intros.
Ltac zringl :=
  Make_ring_rw3_list ltac:(inv_gen_phiZ 0 1 Zplus Zmult Zopp)
    (ring_rw_id_correct (Eqsth Z) (Eq_ext _ _ _)
      (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok)
    (eq (A:=Z))
(BinList.cons ((a+b)*(a+b)) (BinList.nil _)).

Open Scope Z_scope.

let Cst_tac := inv_gen_phiZ 0 1 Zplus Zmult Zopp in
let lemma :=
    constr:(ring_rw_id_correct' (Eqsth Z) (Eq_ext _ _ _)
             (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok) in
let req := constr:(eq (A:=Z)) in
let rl := constr:(cons ((a+b)*(a+b)) (nil _)) in
Make_ring_rw_list Cst_tac lemma req rl.

let fv := constr:(cons a (cons b (nil _))) in
let pe :=
  constr:(PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2))) in
Make_ring_rewrite_step (lemma fv) pe.




OK

Lemma L0 :
 forall (l : list Z) (pe : PExpr Z) pe',
       pe' = norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool pe ->
       PEeval 0 Zplus Zmult Zminus Zopp (IDphi (R:=Z)) l pe =
       Pphi_dev 0 1 Zplus Zmult 0 1 Zeq_bool (IDphi (R:=Z)) l pe'.
intros;  subst pe'.
apply
 (ring_rw_id_correct (Eqsth Z) (Eq_ext _ _ _)
    (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok).
Qed.
Lemma L0' :
 forall (l : list Z) (pe : PExpr Z) pe',
       norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool pe = pe' ->
       PEeval 0 Zplus Zmult Zminus Zopp (IDphi (R:=Z)) l pe =
       Pphi_dev 0 1 Zplus Zmult 0 1 Zeq_bool (IDphi (R:=Z)) l pe'.
intros;  subst pe'.
apply
 (ring_rw_id_correct (Eqsth Z) (Eq_ext _ _ _)
    (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok).
Qed.

pose (pe:=PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2))).
compute_assertion ipattern:H (norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool pe).
let fv := constr:(cons a (cons b (nil _))) in
assert (Heq := L0 fv _ (sym_equal H)); clear H.
 protect_fv' in Heq.
 rewrite Heq; clear Heq; clear pe.


MIEUX (mais taille preuve = taille de pe + taille de nf(pe)... ):


Lemma L :
 forall (l : list Z) (pe : PExpr Z) pe' (x y :Z),
       pe' = norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool pe ->
       x = PEeval 0 Zplus Zmult Zminus Zopp (IDphi (R:=Z)) l pe ->
       y = Pphi_dev 0 1 Zplus Zmult 0 1 Zeq_bool (IDphi (R:=Z)) l pe' ->
       x=y.
intros;  subst x y pe'.
apply
 (ring_rw_id_correct (Eqsth Z) (Eq_ext _ _ _)
    (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok).
Qed.
Lemma L' :
 forall (l : list Z) (pe : PExpr Z) pe' (x y :Z),
       Peq Zeq_bool pe'  (norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool pe) = true ->
       x = PEeval 0 Zplus Zmult Zminus Zopp (IDphi (R:=Z)) l pe ->
       y = Pphi_dev 0 1 Zplus Zmult 0 1 Zeq_bool (IDphi (R:=Z)) l pe' ->
       forall (P:Z->Type), P y -> P x.
intros.
 rewrite L with (2:=H0) (3:=H1); trivial.
apply (Peq_ok (Eqsth Z) (Eq_ext _ _ _)
   (IDmorph 0 1 Zplus Zminus Zmult Zopp (Eqsth Z) Zeq_bool Zeqb_ok) ).

  (IDmorph (Eqsth Z) (Eq_ext _ _ _) Zeqb_ok).


    (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth)).
Qed.

eapply L'
 with (x:=(a+b)*(a+b))
      (pe:=PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2)))
      (l:=cons a (cons b (nil Z)));[compute;reflexivity|reflexivity|idtac|idtac];norm_evars;[protect_fv';reflexivity|idtac];norm_evars.





set (x:=a).
set (x0:=b).
set (fv:=cons x (cons x0 (nil Z))).
let fv:=constr:(cons a (cons b (nil Z))) in
let lemma := constr : (ring_rw_id_correct (Eqsth Z) (Eq_ext _ _ _)
      (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok) in
let pe :=
  constr :  (PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2))) in
assert (Heq := lemma fv pe).
set (npe:=norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool
             (PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2)))).
fold npe in Heq.
move npe after fv.
let fv' := eval red in fv in
compute in npe.
subst npe.
let fv' := eval red in fv in
compute_without_globals_of (fv',Zplus,0,1,Zmult,Zopp,Zminus) in Heq.
rewrite Heq.
clear Heq fv; subst x x0.


simpl in Heq.
unfold Pphi_dev in Heq.
unfold mult_dev in Heq.
unfold P0, Peq in *.
unfold Zeq_bool at 3, Zcompare, Pcompare in Heq.
unfold fv, hd, tl in Heq.
unfold powl, rev, rev_append in Heq.
unfold mkmult1 in Heq.
unfold mkmult in Heq.
unfold add_mult_dev in |- *.
unfold add_mult_dev at 2 in Heq.
unfold P0, Peq at 1 in Heq.
unfold Zeq_bool at 2 3 4 5 6, Zcompare, Pcompare in Heq.
unfold hd, powl, rev, rev_append in Heq.
unfold mkadd_mult in Heq.
unfold mkmult in Heq.
unfold add_mult_dev in Heq.
unfold P0, Peq in Heq.
unfold Zeq_bool, Zcompare, Pcompare in Heq.
unfold hd,powl, rev,rev_append in Heq.
unfold mkadd_mult in Heq.
unfold mkmult in Heq.
unfold IDphi in Heq.

 fv := cons x (cons x0 (nil Z))
 PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2))
 Heq : PEeval 0 Zplus Zmult Zminus Zopp (IDphi (R:=Z)) fv
          (PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2))) =
        Pphi_dev 0 1 Zplus Zmult 0 1 Zeq_bool (IDphi (R:=Z)) fv
          (norm 0 1 Zplus Zmult Zminus Zopp Zeq_bool
             (PEmul (PEadd (PEX Z 1) (PEX Z 2)) (PEadd (PEX Z 1) (PEX Z 2))))



let Cst_tac := inv_gen_phiZ 0 1 Zplus Zmult Zopp in
let lemma :=
    constr:(ring_rw_id_correct (Eqsth Z) (Eq_ext _ _ _)
             (Rth_ARth (Eqsth Z) (Eq_ext _ _ _) Zth) Zeq_bool Zeqb_ok) in
let req := constr:(eq (A:=Z)) in
let rl := constr:(BinList.cons ((a+b)*(a+b)) (BinList.nil _)) in
  match type of lemma with
    forall (l:list ?R) (pe:PExpr ?C),
    req (PEeval ?rO ?add ?mul ?sub ?opp ?phi l pe) _ =>
  Constant natcst.


Require Import Setoid.
Open Scope nat_scope.

Require Import Ring_th.
Require Import Arith.

Add New Ring natr : (SRth_ARth (Eqsth nat) natSRth)
  Computational nateq_ok
  Constant natcst.


Require Import Rbase.
Open Scope R_scope.	      

 Lemma Rth : ring_theory 0 1 Rplus Rmult Rminus Ropp (@eq R).
 Proof.
  constructor. exact Rplus_0_l. exact Rplus_comm. 
  intros;symmetry;apply Rplus_assoc.
  exact Rmult_1_l. exact Rmult_comm. 
  intros;symmetry;apply Rmult_assoc.
  exact Rmult_plus_distr_r. trivial. exact Rplus_opp_r.
 Qed.

Add New Ring Rr : Rth Abstract.

Goal forall a b, (a+b*10)*(a+b*10)=1.
intros.

Module Zring.
  Import Zpol.
  Import BinPos.
  Import BinInt.

Ltac is_PCst p :=
 match p with
 | xH => true
 | (xO ?p') => is_PCst p'
 | (xI ?p') => is_PCst p'
 | _ => false
 end.

Ltac ZCst t :=
 match t with
 | Z0 => constr:t 
 | (Zpos ?p) =>
    match (is_PCst p) with
    | false => NotConstant
    | _ => constr:t
    end
 | (Zneg ?p) =>
    match (is_PCst p) with
    | false => NotConstant
    | _ => constr:t
    end
 | _ => NotConstant
 end.
		  
Ltac zring := 
  Make_ring_tac ZCst
    (Zpol.ring_gen_eq_correct Zth) (Zpol.ring_rw_gen_eq_correct Zth) (@eq Z).

Ltac zrewrite :=
  Make_ring_rw3 ZCst (Zpol.ring_rw_gen_eq_correct Zth) (@eq Z).

Ltac zrewrite_list :=
  Make_ring_rw3_list ZCst (Zpol.ring_rw_gen_eq_correct Zth) (@eq Z).

End Zring.
*)



(*
(*** Intanciation for Z*)
Require Import ZArith.
Open Scope Z_scope.

Module Zring.
  Let R := Z.
  Let rO := 0.
  Let rI := 1.
  Let radd := Zplus.
  Let rmul := Zmult.
  Let rsub := Zminus.
  Let ropp := Zopp.
  Let Rth := Zth.
  Let reqb := Zeq_bool.
  Let req_morph := Zeqb_ok.

  (* CE_Entries *)
  Let C := R.
  Let cO := rO.
  Let cI := rI.
  Let cadd := radd.
  Let cmul := rmul.
  Let csub := rsub.
  Let copp := ropp.
  Let req := (@eq R). 
  Let ceqb := reqb.
  Let phi := @IDphi R.
  Let Rsth : Setoid_Theory R req := Eqsth R.
  Let Reqe : ring_eq_ext radd rmul ropp req :=
   (@Eq_ext R radd rmul ropp).
  Let ARth : almost_ring_theory rO rI radd rmul rsub ropp req :=
   (@Rth_ARth R rO rI radd rmul rsub ropp req Rsth Reqe Rth).
  Let CRmorph : ring_morph rO rI radd rmul rsub ropp req
                           cO cI cadd cmul csub copp ceqb phi :=
   (@IDmorph R rO rI radd rmul rsub ropp req Rsth reqb req_morph).

  Definition Peq := Eval red in (Pol.Peq ceqb).
  Definition mkPinj := Eval red in (@Pol.mkPinj C). 
  Definition mkPX :=
   Eval red;
        change (Pol.Peq ceqb) with Peq;
        change (@Pol.mkPinj Z) with mkPinj in
   (Pol.mkPX cO ceqb). 

  Definition P0 := Eval red in (Pol.P0 cO).
  Definition P1 := Eval red in (Pol.P1 cI).

  Definition X :=
   Eval red; change (Pol.P0 cO) with P0; change (Pol.P1 cI) with P1 in
   (Pol.X cO cI).

  Definition mkX :=
   Eval red; change (Pol.X cO cI) with X in
   (mkX cO cI).

  Definition PaddC
  Definition PaddI
  Definition PaddX

  Definition Padd :=
   Eval red in
        
   (Pol.Padd cO cadd ceqb)

  Definition PmulC
  Definition PmulI
  Definition Pmul_aux
  Definition Pmul

  Definition PsubC
  Definition PsubI
  Definition PsubX
  Definition Psub



  Definition norm :=
   Eval red;
        change (Pol.Padd cO cadd ceqb) with Padd;
        change (Pol.Pmul cO cI cadd cmul ceqb) with Pmul;
        change (Pol.Psub cO cadd csub copp ceqb) with Psub;
        change (Pol.Popp copp) with Psub;
  
 in
   (Pol.norm cO cI cadd cmul csub copp ceqb).



End Zring.
		  
Ltac is_PCst p :=
 match p with
 | xH => true
 | (xO ?p') => is_PCst p'
 | (xI ?p') => is_PCst p'
 | _ => false
 end.

Ltac ZCst t :=
 match t with
 | Z0 => constr:t 
 | (Zpos ?p) =>
    match (is_PCst p) with
    | false => NotConstant
    | _ => t
    end
 | (Zneg ?p) =>
    match (is_PCst p) with
    | false => NotConstant
    | _ => t
    end
 | _ => NotConstant
 end.
		  
Ltac zring := 
  Zring.Make_ring_tac Zplus Zmult Zminus Zopp (@eq Z) ZCst.

Ltac zrewrite :=
  Zring.Make_ring_rw3 Zplus Zmult Zminus Zopp ZCst.
*)

(*	      
(* Instanciation for Bool *)	      
Require Import Bool.
	      
Module BCE.
 Definition R := bool.
 Definition rO := false.
 Definition rI := true.
 Definition radd := xorb.
 Definition rmul := andb.
 Definition rsub := xorb.
 Definition ropp b:bool := b.
 Lemma Rth : ring_theory rO rI radd rmul rsub ropp (@eq bool).
 Proof.
  constructor.
   exact false_xorb.
   exact xorb_comm.
   intros; symmetry  in |- *; apply xorb_assoc.
   exact andb_true_b.
   exact andb_comm.
   exact andb_assoc.
   destruct x; destruct y; destruct z; reflexivity.
   intros; reflexivity.
   exact xorb_nilpotent.
 Qed.

 Definition reqb := eqb.
 Definition req_morph := eqb_prop.
End BCE.

Module BEntries := CE_Entries BCE.

Module Bring := MakeRingPol BEntries.

Ltac BCst t :=
  match t with
   | true => true
   | false => false
   | _ => NotConstant
   end.

Ltac bring := 
  Bring.Make_ring_tac xorb andb xorb (fun b:bool => b) (@eq bool) BCst.

Ltac brewrite :=
  Zring.Make_ring_rw3 Zplus Zmult Zminus Zopp ZCst.
*)

(*Module Rring.

(* Instanciation for R *)	      
Require Import Rbase.
Open Scope R_scope.	      

 Lemma Rth : ring_theory 0 1 Rplus Rmult Rminus Ropp (@eq R).
 Proof.
  constructor. exact Rplus_0_l. exact Rplus_comm. 
  intros;symmetry;apply Rplus_assoc.
  exact Rmult_1_l. exact Rmult_comm. 
  intros;symmetry;apply Rmult_assoc.
  exact Rmult_plus_distr_r. trivial. exact Rplus_opp_r.
 Qed.

Ltac RCst := inv_gen_phiZ 0 1 Rplus Rmul Ropp.

Ltac rring :=
  Make_ring_tac RCst
    (Zpol.ring_gen_eq_correct Rth) (Zpol.ring_rw_gen_eq_correct Rth) (@eq R).

Ltac rrewrite :=
  Make_ring_rw3 RCst (Zpol.ring_rw_gen_eq_correct Rth) (@eq R).

Ltac rrewrite_list :=
  Make_ring_rw3_list RCst (Zpol.ring_rw_gen_eq_correct Rth) (@eq R).

End Rring.
*)
(************************)
(*
(* Instanciation for N *)	     
Require Import NArith.
Open Scope N_scope.
		
Module NCSE.
 Definition R := N.
 Definition rO := 0.
 Definition rI := 1.
 Definition radd := Nplus.
 Definition rmul := Nmult.
 Definition SRth := Nth.
 Definition reqb := Neq_bool.
 Definition req_morph := Neq_bool_ok.
End NCSE.

Module NEntries := CSE_Entries NCSE.

Module Nring := MakeRingPol NEntries.

Ltac NCst := inv_gen_phiN 0 1 Nplus Nmult.

Ltac nring :=  
  Nring.Make_ring_tac Nplus Nmult (@SRsub N Nplus) (@SRopp N) (@eq N) NCst.

Ltac nrewrite :=
  Nring.Make_ring_rw3 Nplus Nmult  (@SRsub N Nplus) (@SRopp N) NCst.
	       
(* Instanciation for nat *)	       
Open Scope nat_scope.

Module NatASE.
 Definition R := nat.
 Definition rO := 0.
 Definition rI := 1.
 Definition radd := plus.
 Definition rmul := mult.
 Lemma SRth : semi_ring_theory O (S O) plus mult (@eq nat).
 Proof.
  constructor. exact plus_0_l. exact plus_comm. exact plus_assoc.
  exact mult_1_l. exact mult_0_l. exact mult_comm. exact mult_assoc.
  exact mult_plus_distr_r. 
 Qed.
End NatASE.

Module NatEntries := ASE_Entries NatASE.

Module Natring := MakeRingPol NatEntries.

Ltac natCst t := 
 match t with
 | O => N0
 | (S ?n) =>
    match (natCst n) with
    | NotConstant => NotConstant
    | ?p => constr:(Nsucc p)
    end
 | _ => NotConstant
 end.
		  
Ltac natring :=
 Natring.Make_ring_tac plus mult (@SRsub nat plus) (@SRopp nat) (@eq nat) natCst.

Ltac natrewrite :=
  Natring.Make_ring_rw3 plus mult (@SRsub nat plus) (@SRopp nat) natCst.
	  
(* Generic tactic, checks the type of the terms and applies the
suitable instanciation*)
		  
Ltac newring :=  
 match goal with
 | |- (?r1 = ?r2) =>
   match (type of r1) with
   | Z => zring
   | R => rring
   | bool => bring
   | N => nring
   | nat => natring
   end
 end.

*)
