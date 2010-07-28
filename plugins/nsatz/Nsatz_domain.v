(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*
 Tactic nsatz: proofs of polynomials equalities in a domain (ring without zero divisor).
 Reification is done by type classes.
 Example: see test-suite/success/Nsatz_domain.v
*)

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Import Ring_polynom Ring_tac InitialRing.
Require Export Morphisms Setoid Bool.

Declare ML Module "nsatz_plugin".

Class Zero (A : Type) := {zero : A}.
Notation "0" := zero.
Class One (A : Type) := {one : A}.
Notation "1" := one.
Class Addition (A : Type) := {addition : A -> A -> A}.
Notation "x + y" := (addition x y).
Class Multiplication (A : Type) := {multiplication : A -> A -> A}.
Notation "x * y" := (multiplication x y).
Class Subtraction (A : Type) := {subtraction : A -> A -> A}.
Notation "x - y" := (subtraction x y).
Class Opposite (A : Type) := {opposite : A -> A}.
Notation "- x" := (opposite x).

Class Ring (R:Type) := {
 ring0: R; ring1: R; 
 ring_plus: R->R->R; ring_mult: R->R->R; 
 ring_sub:  R->R->R; ring_opp: R->R; 
 ring_eq : R -> R -> Prop;
 ring_ring: 
   ring_theory ring0 ring1 ring_plus ring_mult ring_sub 
               ring_opp ring_eq;
 ring_setoid: Equivalence ring_eq;
 ring_plus_comp: Proper (ring_eq==>ring_eq==>ring_eq) ring_plus;
 ring_mult_comp: Proper (ring_eq==>ring_eq==>ring_eq) ring_mult;
 ring_sub_comp: Proper (ring_eq==>ring_eq==>ring_eq) ring_sub;
 ring_opp_comp: Proper (ring_eq==>ring_eq) ring_opp
}.

Class Domain (R : Type) := {
 domain_ring:> Ring R;
 domain_axiom_product:
   forall x y, ring_eq (ring_mult x y) ring0 -> (ring_eq x ring0) \/ (ring_eq y ring0);
 domain_axiom_one_zero: not (ring_eq ring1 ring0)}.

Section domain.

Variable R: Type.
Variable Rd: Domain R.

Existing Instance ring_setoid.
Existing Instance ring_plus_comp.
Existing Instance ring_mult_comp.
Existing Instance ring_sub_comp.
Existing Instance ring_opp_comp.

Add Ring Rr: (@ring_ring R (@domain_ring R Rd)).

Instance zero_ring : Zero R := {zero := ring0}.
Instance one_ring : One R := {one := ring1}.
Instance addition_ring : Addition R := {addition x y := ring_plus x y}.
Instance multiplication_ring : Multiplication R := {multiplication x y := ring_mult x y}.
Instance subtraction_ring : Subtraction R := {subtraction x y := ring_sub x y}.
Instance opposite_ring : Opposite R := {opposite x := ring_opp x}.

Infix "==" := ring_eq (at level 70, no associativity).

Lemma psos_r1b: forall x y:R, x - y == 0 -> x == y.
intros x y H; setoid_replace x with ((x - y) + y); simpl;
 [setoid_rewrite H | idtac]; simpl; ring.
Qed.

Lemma psos_r1: forall x y, x == y -> x - y == 0.
intros x y H; simpl; setoid_rewrite H; simpl; ring.
Qed.

Lemma nsatzR_diff: forall x y:R, not (x == y) -> not (x - y == 0).
intros.
intro; apply H.
simpl; setoid_replace x with ((x - y) + y). simpl.
setoid_rewrite H0.
simpl; ring.
simpl. simpl; ring.
Qed.

(* adpatation du code de Benjamin aux setoides *)
Require Import ZArith.

Definition PolZ := Pol Z.
Definition PEZ := PExpr Z.

Definition P0Z : PolZ := @P0 Z 0%Z.

Definition PolZadd : PolZ -> PolZ -> PolZ :=
  @Padd Z 0%Z Zplus Zeq_bool.

Definition PolZmul : PolZ -> PolZ -> PolZ :=
  @Pmul Z 0%Z 1%Z Zplus Zmult Zeq_bool.

Definition PolZeq := @Peq Z Zeq_bool.

Definition norm :=
  @norm_aux Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool.

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
  (Pphi 0 ring_plus ring_mult (gen_phiZ 0 1 ring_plus ring_mult ring_opp)).

Definition pow (r : R) (n : nat) := pow_N 1 ring_mult r (Nnat.N_of_nat n).

Definition PEevalR : list R -> PEZ -> R :=
   PEeval 0 ring_plus ring_mult ring_sub ring_opp 
    (gen_phiZ 0 1 ring_plus ring_mult ring_opp)
         Nnat.nat_of_N pow.

Lemma P0Z_correct : forall l, PhiR l P0Z = 0.
Proof. trivial. Qed.

Lemma Rext: ring_eq_ext ring_plus ring_mult ring_opp ring_eq.
apply mk_reqe. intros. setoid_rewrite H; rewrite H0; ring.
 intros. setoid_rewrite H; setoid_rewrite H0; ring. 
intros. setoid_rewrite H; ring. Qed.
 
Lemma Rset : Setoid_Theory R ring_eq.
apply ring_setoid.
Qed.

Lemma PolZadd_correct : forall P' P l,
  PhiR l (PolZadd P P') == ((PhiR l P) + (PhiR l P')).
Proof.
simpl.
 refine (Padd_ok Rset Rext (Rth_ARth Rset Rext (@ring_ring _ (@domain_ring _ Rd)))
           (gen_phiZ_morph Rset Rext (@ring_ring _ (@domain_ring _ Rd)))).
Qed.

Lemma PolZmul_correct : forall P P' l,
  PhiR l (PolZmul P P') == ((PhiR l P) * (PhiR l P')).
Proof.
 refine (Pmul_ok Rset Rext (Rth_ARth Rset Rext (@ring_ring _ (@domain_ring _ Rd)))
           (gen_phiZ_morph Rset Rext (@ring_ring _ (@domain_ring _ Rd)))).
Qed.

Lemma R_power_theory
     : power_theory 1 ring_mult ring_eq Nnat.nat_of_N pow.
apply mkpow_th. unfold pow. intros. rewrite Nnat.N_of_nat_of_N. ring. Qed. 

Lemma norm_correct :
  forall (l : list R) (pe : PEZ), PEevalR l pe == PhiR l (norm pe).
Proof.
 intros;apply (norm_aux_spec Rset Rext (Rth_ARth Rset Rext (@ring_ring _ (@domain_ring _ Rd)))
           (gen_phiZ_morph Rset Rext (@ring_ring _ (@domain_ring _ Rd))) R_power_theory)
    with (lmp:= List.nil).
 compute;trivial.
Qed.

Lemma PolZeq_correct : forall P P' l,
  PolZeq P P' = true ->
  PhiR l P == PhiR l P'.
Proof.
 intros;apply
   (Peq_ok Rset Rext (gen_phiZ_morph Rset Rext (@ring_ring _ (@domain_ring _ Rd))));trivial.
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
 induction la;simpl;intros. ring.
 destruct lp;trivial. simpl. ring.
 simpl in H;destruct H.
 setoid_rewrite  PolZadd_correct.
 simpl. setoid_rewrite PolZmul_correct. simpl. setoid_rewrite  H.
 setoid_rewrite IHla. unfold zero. simpl. ring. trivial.
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

Lemma pow_not_zero: forall p n, pow p n == 0 -> p == 0.
induction n. unfold pow; simpl. intros. absurd (1 == 0). 
simpl. apply domain_axiom_one_zero.
 trivial. setoid_replace (pow p (S n)) with (p * (pow p n)). intros. 
case (@domain_axiom_product _ _ _ _ H). trivial. trivial. 
unfold pow; simpl. 
clear IHn. induction n; simpl; try ring. 
 rewrite pow_pos_Psucc. ring. exact Rset.
 intros. setoid_rewrite H; setoid_rewrite H0; ring.
 intros. simpl; ring. intros. simpl; ring. Qed.

Lemma Rdomain_pow: forall c p r, ~c == ring0 -> ring_mult c (pow p r) == ring0 -> p == ring0.
intros. case (@domain_axiom_product _ _ _ _ H0). intros; absurd (c == ring0); auto. 
intros. apply pow_not_zero with r. trivial. Qed.   

Definition R2:= ring_plus ring1 ring1.

Fixpoint IPR p {struct p}: R :=
  match p with
    xH => ring1
  | xO xH => ring_plus ring1 ring1
  | xO p1 => ring_mult R2 (IPR p1)
  | xI xH => ring_plus ring1 (ring_plus ring1 ring1)
  | xI p1 => ring_plus ring1 (ring_mult R2 (IPR p1))
  end.

Definition IZR1 z :=
  match z with Z0 => ring0
             | Zpos p => IPR p
             | Zneg p => ring_opp(IPR p)
  end.

Fixpoint interpret3 t fv {struct t}: R :=
  match t with
  | (PEadd t1 t2) =>
       let v1  := interpret3 t1 fv in
       let v2  := interpret3 t2 fv in (ring_plus v1 v2)
  | (PEmul t1 t2) =>
       let v1  := interpret3 t1 fv in
       let v2  := interpret3 t2 fv in (ring_mult v1 v2)
  | (PEsub t1 t2) =>
       let v1  := interpret3 t1 fv in
       let v2  := interpret3 t2 fv in (ring_sub v1 v2)
  | (PEopp t1) =>
       let v1  := interpret3 t1 fv in (ring_opp v1)
  | (PEpow t1 t2) =>
       let v1  := interpret3 t1 fv in pow v1 (Nnat.nat_of_N t2)
  | (PEc t1) => (IZR1 t1)
  | (PEX n) => List.nth (pred (nat_of_P n)) fv 0
  end.


End domain.

Ltac equalities_to_goal :=
  lazymatch goal with
  |  H: (@ring_eq _ _ ?x ?y) |- _ =>
          try generalize (@psos_r1 _ _ _ _ H); clear H
   end.

Ltac nsatz_domain_begin tacsimpl :=
  intros;
  try apply (@psos_r1b _ _);
  repeat equalities_to_goal;
  tacsimpl.

Ltac generalise_eq_hyps:=
  repeat
    (match goal with
     |h : (@ring_eq _ _ ?p ?q)|- _ => revert h
     end).

Ltac lpol_goal t :=
  match t with
  | ?a = ring0 -> ?b =>
    let r:= lpol_goal b in
    constr:(a::r)
  | ?a = ring0 => constr:(a::nil)
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
  (*idtac "Trying power: " rr;*)
  let ll := constr:(PEc info :: PEc nparam :: PEpow p rr :: lp) in
  nsatz_compute ll; 
  (*idtac "done";*)
  match goal with
  | |- (?c::PEpow _ ?r::?lq0)::?lci0 = _ -> _ =>
    intros _;
    set (lci:=lci0);
    set (lq:=lq0);
    kont c rr lq lci
  end.

Ltac nsatz_call radicalmax info nparam p lp kont :=
  let rec try_n n :=
    lazymatch n with
    | 0%N => fail
    | _ =>
        (let r := eval compute in (Nminus radicalmax (Npred n)) in
         nsatz_call_n info nparam p r lp kont) ||
         let n' := eval compute in (Npred n) in try_n n'
    end in
  try_n radicalmax.


Set Implicit Arguments.
Class Cclosed_seq T (l:list T) := {}.
Instance Iclosed_nil T : Cclosed_seq (T:=T) nil.
Instance Iclosed_cons T t l `{Cclosed_seq (T:=T) l} : Cclosed_seq (T:=T) (t::l).

Class Cfind_at (R:Type) (b:R) (l:list R) (i:nat) := {}.
Instance  Ifind0 (R:Type) (b:R) l: Cfind_at b (b::l) 0.
Instance  IfindS (R:Type) (b2 b1:R) l i `{Cfind_at R b1 l i} : Cfind_at b1 (b2::l) (S i) | 1.
Definition Ifind0' := Ifind0.
Definition IfindS' := IfindS.

Definition li_find_at (R:Type) (b:R) l i `{Cfind_at R b l i} {H:Cclosed_seq (T:=R) l} := (l,i).

Class Creify (R:Type) (e:PExpr Z) (l:list R) (b:R) := {}.
Instance  Ireify_zero (R:Type) (Rd:Domain R) l : Creify (PEc 0%Z) l ring0.
Instance  Ireify_one (R:Type)  (Rd:Domain R) l : Creify (PEc 1%Z) l ring1.
Instance  Ireify_plus (R:Type)  (Rd:Domain R) e1 l b1 e2 b2 `{Creify R e1 l b1} `{Creify R e2 l b2} 
 : Creify (PEadd e1 e2) l (ring_plus b1 b2).
Instance  Ireify_mult (R:Type)  (Rd:Domain R) e1 l b1 e2 b2 `{Creify R e1 l b1} `{Creify R e2 l b2}
 : Creify (PEmul e1 e2) l (ring_mult b1 b2).
Instance  Ireify_sub (R:Type) (Rd:Domain R) e1 l b1 e2 b2 `{Creify R e1 l b1} `{Creify R e2 l b2}
 : Creify (PEsub e1 e2) l (ring_sub b1 b2).
Instance  Ireify_opp (R:Type) (Rd:Domain R) e1 l b1 `{Creify R e1 l b1}
 : Creify (PEopp e1) l (ring_opp b1).
Instance  Ireify_var (R:Type) b l i `{Cfind_at R b l i}
 : Creify (PEX _ (P_of_succ_nat i)) l b | 100.


Class Creifylist (R:Type) (le:list (PExpr Z)) (l:list R) (lb:list R) := {}.
Instance Creify_nil (R:Type) l : Creifylist nil l (@nil R).
Instance Creify_cons (R:Type) e1 l b1 le2 lb2 `{Creify R e1 l b1} `{Creifylist R le2 l lb2} 
 : Creifylist (e1::le2) l (b1::lb2).

Definition li_reifyl (R:Type) le l lb `{Creifylist R le l lb}
 {H:Cclosed_seq (T:=R) l} := (l,le).

Unset Implicit Arguments.

Ltac lterm_goal g :=
  match g with
  ring_eq ?b1 ?b2 => constr:(b1::b2::nil)
  | ring_eq ?b1 ?b2 -> ?g => let l := lterm_goal g in constr:(b1::b2::l)     
  end.

Ltac reify_goal l le lb Rd:=
  match le with
     nil => idtac
   | ?e::?le1 => 
        match lb with
         ?b::?lb1 => (* idtac "b="; idtac b;*)
           let x := fresh "B" in
           set (x:= b) at 1;
           change x with (@interpret3 _ Rd e l); 
           clear x;
           reify_goal l le1 lb1 Rd
        end
  end.

Ltac get_lpol g :=
  match g with
  ring_eq (interpret3 _ _ ?p _) _ => constr:(p::nil)
  | ring_eq (interpret3 _ _ ?p _) _ -> ?g =>
       let l := get_lpol g in constr:(p::l)     
  end.

Ltac nsatz_domain_generic radicalmax info lparam lvar tacsimpl Rd :=
  match goal with
  |- ?g => let lb := lterm_goal g in
     (*idtac "lb"; idtac lb;*)
     match eval red in (li_reifyl (lb:=lb)) with
     | (?fv, ?le) => 
        let fv := match lvar with
                     (@nil _) => fv
                    | _ => lvar
                  end in
        (* idtac "variables:";idtac fv;*)
        let nparam := eval compute in (Z_of_nat (List.length lparam)) in
        let fv := parametres_en_tete fv lparam in
        (*idtac "variables:"; idtac fv;
        idtac "nparam:"; idtac nparam; *)
        match eval red in (li_reifyl (l:=fv) (lb:=lb)) with
          | (?fv, ?le) => 
              (*idtac "variables:";idtac fv; idtac le; idtac lb;*)
              reify_goal fv le lb Rd;
                match goal with 
                   |- ?g => 
                       let lp := get_lpol g in 
                       let lpol := eval compute in (List.rev lp) in
                       (*idtac "polynomes:"; idtac lpol;*)
                       tacsimpl; intros;
 
  let SplitPolyList kont :=
    match lpol with
    | ?p2::?lp2 => kont p2 lp2
    | _ => idtac "polynomial not in the ideal"
    end in 
  tacsimpl; 
  SplitPolyList ltac:(fun p lp =>
    set (p21:=p) ;
    set (lp21:=lp);
    (*idtac "lp:"; idtac lp; *)
    nsatz_call radicalmax info nparam p lp ltac:(fun c r lq lci => 
      set (q := PEmul c (PEpow p21 r)); 
      let Hg := fresh "Hg" in 
      assert (Hg:check lp21 q (lci,lq) = true); 
      [ (vm_compute;reflexivity) || idtac "invalid nsatz certificate"
      | let Hg2 := fresh "Hg" in 
            assert (Hg2: ring_eq (interpret3 _ Rd q fv) ring0);
        [ tacsimpl; 
          apply (@check_correct _ Rd fv lp21 q (lci,lq) Hg);
          tacsimpl;
          repeat (split;[assumption|idtac]); exact I
        | simpl in Hg2; tacsimpl; 
          apply Rdomain_pow with (interpret3 _ Rd c fv) (Nnat.nat_of_N r); auto with domain;
          tacsimpl; apply domain_axiom_one_zero 
          || (simpl) || idtac "could not prove discrimination result"
        ]
      ]
) 
)
end end end end .

Ltac nsatz_domainpv pretac radicalmax info lparam lvar tacsimpl rd :=
  pretac;
  nsatz_domain_begin tacsimpl; auto with domain;
  nsatz_domain_generic radicalmax info lparam lvar tacsimpl rd.

Ltac nsatz_domain:= 
  intros;
  match goal with
    |- (@ring_eq _ (@domain_ring ?r ?rd) _ _ ) =>
          nsatz_domainpv ltac:idtac 6%N 1%Z (@nil r) (@nil r) ltac:(simpl) rd
  end.

(* Dans R *)
Require Import Reals.
Require Import RealField.

Instance Rri : Ring R := {
  ring0 := 0%R;
  ring1 := 1%R;
  ring_plus := Rplus;
  ring_mult := Rmult;
  ring_sub := Rminus;
  ring_opp := Ropp; 
  ring_eq := @eq R; 
  ring_ring := RTheory}.

Lemma Raxiom_one_zero: 1%R <> 0%R.
discrR.
Qed.

Instance Rdi : Domain R := {
  domain_ring := Rri;
  domain_axiom_product := Rmult_integral;
  domain_axiom_one_zero := Raxiom_one_zero}.

Hint Resolve ring_setoid ring_plus_comp ring_mult_comp ring_sub_comp ring_opp_comp: domain.

Ltac replaceR:=
replace 0%R with (@ring0 _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity];
replace 1%R with (@ring1 _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity];
replace Rplus with (@ring_plus _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity];
replace Rmult with (@ring_mult _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity];
replace Rminus with (@ring_sub _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity];
replace Ropp with (@ring_opp _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity];
replace (@eq R) with (@ring_eq _ (@domain_ring _ Rdi)) in *;[idtac|reflexivity].

Ltac simplR:=
  simpl; replaceR.

Ltac pretacR:=
  replaceR;
  replace Rri with (@domain_ring _ Rdi) in *; [idtac | reflexivity].

Ltac nsatz_domainR:= 
  nsatz_domainpv ltac:pretacR 6%N 1%Z (@Datatypes.nil R) (@Datatypes.nil R)
    ltac:simplR Rdi;
  discrR.


Goal forall x y:R, x = y -> (x*x-x+1)%R = ((y*y-y)+1+0)%R.
nsatz_domainR.
Qed.


(* Dans Z *)
Instance Zri : Ring Z := {
  ring0 := 0%Z;
  ring1 := 1%Z;
  ring_plus := Zplus;
  ring_mult := Zmult;
  ring_sub := Zminus;
  ring_opp := Zopp; 
  ring_eq := (@eq Z); 
  ring_ring := Zth}.

Lemma Zaxiom_one_zero: 1%Z <> 0%Z.
discriminate.
Qed.

Instance Zdi : Domain Z := {
  domain_ring := Zri;
  domain_axiom_product := Zmult_integral;
  domain_axiom_one_zero := Zaxiom_one_zero}.

Ltac replaceZ :=
replace 0%Z with (@ring0 _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity];
replace 1%Z with (@ring1 _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity];
replace Zplus with (@ring_plus _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity];
replace Zmult with (@ring_mult _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity];
replace Zminus with (@ring_sub _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity];
replace Zopp with (@ring_opp _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity];
replace (@eq Z) with (@ring_eq _ (@domain_ring _ Zdi)) in *;[idtac|reflexivity].

Ltac simplZ:=
  simpl; replaceZ.

Ltac pretacZ :=
replaceZ;
replace Zri with (@domain_ring _ Zdi) in *; [idtac | reflexivity].

Ltac nsatz_domainZ:= 
nsatz_domainpv ltac:pretacZ 6%N 1%Z (@Datatypes.nil Z) (@Datatypes.nil Z) ltac:simplZ Zdi.


(* Dans Q *)
Require Import QArith.

Instance Qri : Ring Q := {
  ring0 := 0%Q;
  ring1 := 1%Q;
  ring_plus := Qplus;
  ring_mult := Qmult;
  ring_sub := Qminus;
  ring_opp := Qopp; 
  ring_eq := Qeq; 
  ring_ring := Qsrt}.

Lemma Qaxiom_one_zero: not (Qeq 1%Q 0%Q).
discriminate.
Qed.

Instance Qdi : Domain Q := {
  domain_ring := Qri;
  domain_axiom_product := Qmult_integral;
  domain_axiom_one_zero := Qaxiom_one_zero}.

Ltac replaceQ :=
replace 0%Q with (@ring0 _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity];
replace 1%Q with (@ring1 _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity];
replace Qplus with (@ring_plus _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity];
replace Qmult with (@ring_mult _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity];
replace Qminus with (@ring_sub _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity];
replace Qopp with (@ring_opp _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity];
replace Qeq with (@ring_eq _ (@domain_ring _ Qdi)) in *;[idtac|reflexivity].

Ltac simplQ:=
  simpl; replaceQ.

Ltac pretacQ := 
replaceQ;
replace Qri with (@domain_ring _ Qdi) in *; [idtac | reflexivity].

Ltac nsatz_domainQ:= 
nsatz_domainpv ltac:pretacQ 6%N 1%Z (@Datatypes.nil Q) (@Datatypes.nil Q) ltac:simplQ Qdi.

(* tactique générique *)

Ltac nsatz :=
  intros;
  match goal with
   | |- (@eq R _ _) => nsatz_domainR
   | |- (@eq Z _ _) => nsatz_domainZ
   | |- (@Qeq _ _) => nsatz_domainQ
   | |- _ => nsatz_domain
  end.
(*
Goal forall x y:Q, Qeq x y -> Qeq (x*x-x+1)%Q ((y*y-y)+1+0)%Q.
nsatz.
Qed.

Goal forall x y:Z, x = y -> (x*x-x+1)%Z = ((y*y-y)+1+0)%Z.
nsatz.
Qed.

Goal forall x y:R, x = y -> (x*x-x+1)%R = ((y*y-y)+1+0)%R.
nsatz.
Qed.
*)
