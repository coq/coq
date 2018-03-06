(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
 Tactic nsatz: proofs of polynomials equalities in an integral domain 
(commutative ring without zero divisor).
 
Examples: see test-suite/success/Nsatz.v

Reification is done using type classes, defined in Ncring_tac.v

*)

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Export Algebra_syntax.
Require Export Ncring.
Require Export Ncring_initial.
Require Export Ncring_tac.
Require Export Integral_domain.
Require Import DiscrR.
Require Import ZArith.

Declare ML Module "nsatz_plugin".

Section nsatz1.

Context {R:Type}`{Rid:Integral_domain R}.

Lemma psos_r1b: forall x y:R, x - y == 0 -> x == y.
intros x y H; setoid_replace x with ((x - y) + y); simpl;
 [setoid_rewrite H | idtac]; simpl. cring. cring.
Qed.

Lemma psos_r1: forall x y, x == y -> x - y == 0.
intros x y H; simpl; setoid_rewrite H; simpl; cring.
Qed.

Lemma nsatzR_diff: forall x y:R, not (x == y) -> not (x - y == 0).
intros.
intro; apply H.
simpl; setoid_replace x with ((x - y) + y). simpl.
setoid_rewrite H0.
simpl; cring.
simpl. simpl; cring.
Qed.

(* adpatation du code de Benjamin aux setoides *)
Export Ring_polynom.
Export InitialRing.

Definition PolZ := Pol Z.
Definition PEZ := PExpr Z.

Definition P0Z : PolZ := P0 (C:=Z) 0%Z.

Definition PolZadd : PolZ -> PolZ -> PolZ :=
  @Padd  Z 0%Z Z.add Zeq_bool.

Definition PolZmul : PolZ -> PolZ -> PolZ :=
  @Pmul  Z 0%Z 1%Z Z.add Z.mul Zeq_bool.

Definition PolZeq := @Peq Z Zeq_bool.

Definition norm :=
  @norm_aux Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zeq_bool.

Fixpoint mult_l (la : list PEZ) (lp: list PolZ) : PolZ :=
 match la, lp with
 | a::la, p::lp => PolZadd (PolZmul (norm a) p) (mult_l la lp)
 | _, _ => P0Z
 end.

Fixpoint compute_list (lla: list (list PEZ)) (lp:list PolZ) :=
 match lla with
 | List.nil => lp
 | la::lla => compute_list lla ((mult_l la lp)::lp)
 end.

Definition check (lpe:list PEZ) (qe:PEZ) (certif: list (list PEZ) * list PEZ) :=
 let (lla, lq) := certif in
 let lp := List.map norm lpe in
 PolZeq (norm qe) (mult_l lq (compute_list lla lp)).


(* Correction *)
Definition PhiR : list R -> PolZ -> R :=
  (Pphi ring0 add mul 
    (InitialRing.gen_phiZ ring0 ring1 add mul opp)).

Definition PEevalR : list R -> PEZ -> R :=
   PEeval ring0 ring1 add mul sub opp
    (gen_phiZ ring0 ring1 add mul opp)
         N.to_nat pow.

Lemma P0Z_correct : forall l, PhiR l P0Z = 0.
Proof. trivial. Qed.

Lemma Rext: ring_eq_ext add mul opp _==_.
Proof.
constructor; solve_proper.
Qed.

Lemma Rset : Setoid_Theory R _==_.
apply ring_setoid.
Qed.

Definition Rtheory:ring_theory ring0 ring1 add mul sub opp _==_.
apply mk_rt.
apply ring_add_0_l.
apply ring_add_comm.   
apply ring_add_assoc.  
apply ring_mul_1_l.    
apply cring_mul_comm.
apply ring_mul_assoc.
apply ring_distr_l.    
apply ring_sub_def.  
apply ring_opp_def.
Defined.

Lemma PolZadd_correct : forall P' P l,
  PhiR l (PolZadd P P') == ((PhiR l P) + (PhiR l P')).
Proof.
unfold PolZadd, PhiR. intros. simpl.
 refine (Padd_ok Rset Rext (Rth_ARth Rset Rext Rtheory)
           (gen_phiZ_morph Rset Rext Rtheory) _ _ _).
Qed.

Lemma PolZmul_correct : forall P P' l,
  PhiR l (PolZmul P P') == ((PhiR l P) * (PhiR l P')).
Proof.
unfold PolZmul, PhiR. intros. 
 refine (Pmul_ok Rset Rext (Rth_ARth Rset Rext Rtheory)
           (gen_phiZ_morph Rset Rext Rtheory) _ _ _).
Qed.

Lemma R_power_theory
     : Ring_theory.power_theory ring1 mul _==_ N.to_nat pow.
apply Ring_theory.mkpow_th. unfold pow. intros. rewrite Nnat.N2Nat.id.
reflexivity. Qed.

Lemma norm_correct :
  forall (l : list R) (pe : PEZ), PEevalR l pe == PhiR l (norm pe).
Proof.
 intros;apply (norm_aux_spec Rset Rext (Rth_ARth Rset Rext Rtheory)
           (gen_phiZ_morph Rset Rext Rtheory) R_power_theory).
Qed.

Lemma PolZeq_correct : forall P P' l,
  PolZeq P P' = true ->
  PhiR l P == PhiR l P'.
Proof.
 intros;apply
   (Peq_ok Rset Rext (gen_phiZ_morph Rset Rext Rtheory));trivial.
Qed.

Fixpoint Cond0 (A:Type) (Interp:A->R) (l:list A) : Prop :=
  match l with
  | List.nil => True
  | a::l => Interp a == 0 /\ Cond0 A Interp l
  end.

Lemma mult_l_correct : forall l la lp,
  Cond0 PolZ (PhiR l) lp ->
  PhiR l (mult_l la lp) == 0.
Proof.
 induction la;simpl;intros. cring.
 destruct lp;trivial. simpl. cring.
 simpl in H;destruct H.
 rewrite  PolZadd_correct.
 simpl. rewrite PolZmul_correct. simpl. rewrite  H.
 rewrite IHla. cring. trivial.
Qed.

Lemma compute_list_correct : forall l lla lp,
  Cond0 PolZ (PhiR l) lp ->
  Cond0 PolZ (PhiR l) (compute_list lla lp).
Proof.
 induction lla;simpl;intros;trivial.
 apply IHlla;simpl;split;trivial.
 apply mult_l_correct;trivial.
Qed.

Lemma check_correct :
  forall l lpe qe certif,
    check lpe qe certif = true ->
    Cond0 PEZ (PEevalR l) lpe ->
    PEevalR l qe == 0.
Proof.
 unfold check;intros l lpe qe (lla, lq) H2 H1.
 apply PolZeq_correct with (l:=l) in H2.
 rewrite norm_correct, H2.
 apply mult_l_correct.
 apply compute_list_correct.
 clear H2 lq lla qe;induction lpe;simpl;trivial.
 simpl in H1;destruct H1.
 rewrite <- norm_correct;auto.
Qed.

(* fin *)

Definition R2:= 1 + 1.

Fixpoint IPR p {struct p}: R :=
  match p with
    xH => ring1
  | xO xH => 1+1
  | xO p1 => R2*(IPR p1)
  | xI xH => 1+(1+1)
  | xI p1 => 1+(R2*(IPR p1))
  end.

Definition IZR1 z :=
  match z with Z0 => 0
             | Zpos p => IPR p
             | Zneg p => -(IPR p)
  end.

Fixpoint interpret3 t fv {struct t}: R :=
  match t with
  | (PEadd t1 t2) =>
       let v1  := interpret3 t1 fv in
       let v2  := interpret3 t2 fv in (v1 + v2)
  | (PEmul t1 t2) =>
       let v1  := interpret3 t1 fv in
       let v2  := interpret3 t2 fv in (v1 * v2)
  | (PEsub t1 t2) =>
       let v1  := interpret3 t1 fv in
       let v2  := interpret3 t2 fv in (v1 - v2)
  | (PEopp t1) =>
       let v1  := interpret3 t1 fv in (-v1)
  | (PEpow t1 t2) =>
       let v1  := interpret3 t1 fv in pow v1 (N.to_nat t2)
  | (PEc t1) => (IZR1 t1)
  | PEO => 0
  | PEI => 1
  | (PEX _ n) => List.nth (pred (Pos.to_nat n)) fv 0
  end.


End nsatz1.

Ltac equality_to_goal H x y:=
  (* eliminate trivial  hypotheses, but it takes time!:
  let h := fresh "nH" in
    (assert (h:equality x y);
    [solve [cring] | clear H; clear h])
  || *) try (generalize (@psos_r1 _ _ _ _ _ _ _ _ _ _ _ x y H); clear H)
.

Ltac equalities_to_goal :=
  lazymatch goal with
  |  H: (_ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ _ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ _ _ ?x ?y) |- _ => equality_to_goal H x y
(* extension possible :-) *)
  |  H: (?x == ?y) |- _ => equality_to_goal H x y
   end.

(* lp est incluse dans fv. La met en tete. *)

Ltac parametres_en_tete fv lp :=
    match fv with
     | (@nil _)          => lp
     | (@cons _ ?x ?fv1) =>
       let res := AddFvTail x lp in
         parametres_en_tete fv1 res
    end.

Ltac append1 a l :=
 match l with
 | (@nil _)     => constr:(cons a l)
 | (cons ?x ?l) => let l' := append1 a l in constr:(cons x l')
 end.

Ltac rev l :=
  match l with
   |(@nil _)      => l
   | (cons ?x ?l) => let l' := rev l in append1 x l'
  end.

Ltac nsatz_call_n info nparam p rr lp kont := 
(*  idtac "Trying power: " rr;*)
  let ll := constr:(PEc info :: PEc nparam :: PEpow p rr :: lp) in
(*  idtac "calcul...";*)
  nsatz_compute ll; 
(*  idtac "done";*)
  match goal with
  | |- (?c::PEpow _ ?r::?lq0)::?lci0 = _ -> _ =>
    intros _;
    let lci := fresh "lci" in
    set (lci:=lci0);
    let lq := fresh "lq" in
    set (lq:=lq0);
    kont c rr lq lci
  end.

Ltac nsatz_call radicalmax info nparam p lp kont :=
  let rec try_n n :=
    lazymatch n with
    | 0%N => fail
    | _ =>
        (let r := eval compute in (N.sub radicalmax (N.pred n)) in
         nsatz_call_n info nparam p r lp kont) ||
         let n' := eval compute in (N.pred n) in try_n n'
    end in
  try_n radicalmax.


Ltac lterm_goal g :=
  match g with
    ?b1 == ?b2 => constr:(b1::b2::nil)
  | ?b1 == ?b2 -> ?g => let l := lterm_goal g in constr:(b1::b2::l)     
  end.

Ltac reify_goal l le lb:=
  match le with
     nil => idtac
   | ?e::?le1 => 
        match lb with
         ?b::?lb1 => (* idtac "b="; idtac b;*)
           let x := fresh "B" in
           set (x:= b) at 1;
           change x with (interpret3 e l); 
           clear x;
           reify_goal l le1 lb1
        end
  end.

Ltac get_lpol g :=
  match g with
  (interpret3 ?p _) == _ => constr:(p::nil)
  | (interpret3 ?p _) == _ -> ?g =>
       let l := get_lpol g in constr:(p::l)     
  end.

Ltac nsatz_generic radicalmax info lparam lvar :=
 let nparam := eval compute in (Z.of_nat (List.length lparam)) in
 match goal with
  |- ?g => let lb := lterm_goal g in 
     match (match lvar with
              |(@nil _) =>
                 match lparam with
                   |(@nil _) =>
                     let r := eval red in (list_reifyl (lterm:=lb)) in r
                   |_ =>
                     match eval red in (list_reifyl (lterm:=lb)) with
                       |(?fv, ?le) =>
                         let fv := parametres_en_tete fv lparam in
                           (* we reify a second time, with the good order
                              for variables *)
                         let r := eval red in 
                                  (list_reifyl (lterm:=lb) (lvar:=fv)) in r
                     end
                  end
              |_ => 
                let fv := parametres_en_tete lvar lparam in
                let r := eval red in (list_reifyl (lterm:=lb) (lvar:=fv)) in r
            end) with
          |(?fv, ?le) => 
            reify_goal fv le lb ;
            match goal with 
                   |- ?g => 
                       let lp := get_lpol g in 
                       let lpol := eval compute in (List.rev lp) in
                       intros;

  let SplitPolyList kont :=
    match lpol with
    | ?p2::?lp2 => kont p2 lp2
    | _ => idtac "polynomial not in the ideal"
    end in 

  SplitPolyList ltac:(fun p lp =>
    let p21 := fresh "p21" in
    let lp21 := fresh "lp21" in
    set (p21:=p) ;
    set (lp21:=lp);
(*    idtac "nparam:"; idtac nparam; idtac "p:"; idtac p; idtac "lp:"; idtac lp; *)
    nsatz_call radicalmax info nparam p lp ltac:(fun c r lq lci => 
      let q := fresh "q" in
      set (q := PEmul c (PEpow p21 r)); 
      let Hg := fresh "Hg" in 
      assert (Hg:check lp21 q (lci,lq) = true); 
      [ (vm_compute;reflexivity) || idtac "invalid nsatz certificate"
      | let Hg2 := fresh "Hg" in 
            assert (Hg2: (interpret3 q fv) == 0);
        [ (*simpl*) idtac; 
          generalize (@check_correct _ _ _ _ _ _ _ _ _ _ _ fv lp21 q (lci,lq) Hg);
          let cc := fresh "H" in
             (*simpl*) idtac; intro cc; apply cc; clear cc;
          (*simpl*) idtac;
          repeat (split;[assumption|idtac]); exact I
        | (*simpl in Hg2;*) (*simpl*) idtac; 
          apply Rintegral_domain_pow with (interpret3 c fv) (N.to_nat r);
          (*simpl*) idtac;
            try apply integral_domain_one_zero;
            try apply integral_domain_minus_one_zero;
            try trivial;
            try exact integral_domain_one_zero;
            try exact integral_domain_minus_one_zero
          || (solve [simpl; unfold R2, equality, eq_notation, addition, add_notation,
                     one, one_notation, multiplication, mul_notation, zero, zero_notation;
                     discrR || omega]) 
          || ((*simpl*) idtac) || idtac "could not prove discrimination result"
        ]
      ]
) 
)
end end end .

Ltac nsatz_default:=
  intros;
  try apply (@psos_r1b _ _ _ _ _ _ _ _ _ _ _);
  match goal with |- (@equality ?r _ _ _) =>
    repeat equalities_to_goal;
    nsatz_generic 6%N 1%Z (@nil r) (@nil r)
  end.

Tactic Notation "nsatz" := nsatz_default.

Tactic Notation "nsatz" "with"
 "radicalmax" ":=" constr(radicalmax) 
 "strategy" ":=" constr(info) 
 "parameters" ":=" constr(lparam)
 "variables" ":=" constr(lvar):=
  intros;
  try apply (@psos_r1b _ _ _ _ _ _ _ _ _ _ _);
  match goal with |- (@equality ?r _ _ _) =>
    repeat equalities_to_goal;
    nsatz_generic radicalmax info lparam lvar
  end.

(* Real numbers *)
Require Import Reals.
Require Import RealField.

Lemma Rsth : Setoid_Theory R (@eq R).
constructor;red;intros;subst;trivial.
Qed.

Instance Rops: (@Ring_ops R 0%R 1%R Rplus Rmult Rminus Ropp (@eq R)).

Instance Rri : (Ring (Ro:=Rops)).
constructor;
try (try apply Rsth;
   try (unfold respectful, Proper; unfold equality; unfold eq_notation in *;
  intros; try rewrite H; try rewrite H0; reflexivity)).
 exact Rplus_0_l. exact Rplus_comm. symmetry. apply Rplus_assoc.
 exact Rmult_1_l.  exact Rmult_1_r. symmetry. apply Rmult_assoc.
 exact Rmult_plus_distr_r. intros; apply Rmult_plus_distr_l. 
exact Rplus_opp_r.
Defined.

Class can_compute_Z (z : Z) := dummy_can_compute_Z : True.
Hint Extern 0 (can_compute_Z ?v) =>
  match isZcst v with true => exact I end : typeclass_instances.
Instance reify_IZR z lvar {_ : can_compute_Z z} : reify (PEc z) lvar (IZR z).

Lemma R_one_zero: 1%R <> 0%R.
discrR.
Qed.

Instance Rcri: (Cring (Rr:=Rri)).
red. exact Rmult_comm. Defined.

Instance Rdi : (Integral_domain (Rcr:=Rcri)). 
constructor. 
exact Rmult_integral. exact R_one_zero. Defined.

(* Rational numbers *)
Require Import QArith.

Instance Qops: (@Ring_ops Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq).

Instance Qri : (Ring (Ro:=Qops)).
constructor.
try apply Q_Setoid. 
apply Qplus_comp. 
apply Qmult_comp. 
apply Qminus_comp. 
apply Qopp_comp.
 exact Qplus_0_l. exact Qplus_comm. apply Qplus_assoc.
 exact Qmult_1_l.  exact Qmult_1_r. apply Qmult_assoc.
 apply Qmult_plus_distr_l.  intros. apply Qmult_plus_distr_r. 
reflexivity. exact Qplus_opp_r.
Defined.

Lemma Q_one_zero: not (Qeq 1%Q 0%Q).
unfold Qeq. simpl. auto with *. Qed.

Instance Qcri: (Cring (Rr:=Qri)).
red. exact Qmult_comm. Defined.

Instance Qdi : (Integral_domain (Rcr:=Qcri)). 
constructor. 
exact Qmult_integral. exact Q_one_zero. Defined.

(* Integers *)
Lemma Z_one_zero: 1%Z <> 0%Z.
omega. 
Qed.

Instance Zcri: (Cring (Rr:=Zr)).
red. exact Z.mul_comm. Defined.

Instance Zdi : (Integral_domain (Rcr:=Zcri)). 
constructor. 
exact Zmult_integral. exact Z_one_zero. Defined.

