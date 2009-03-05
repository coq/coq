(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* 
 Tactic groebnerR: proofs of polynomials equalities with variables in R.
 Use Hilbert Nullstellensatz and Buchberger algorithm (adapted version of
 L.Thery Coq proven implementation).
 Thanks to B.Gregoire and L.Thery for help on ring tactic.
 Examples at the end of the file.
 
 3 versions:
 
 - groebnerR.

 - groebnerRp (a::b::c::nil) : give the list of variables are considered as
   parameters. Computation will be performed with rational fractions in these
   variables.

 - groebnerRpv (a::b::c::nil) (x::y::z::nil): give also the order of the
   variables used in Buchberger algorithm. Here x>y>z.

 Loic Pottier
 19-12-08
*)

Require Import Reals. (* beware that Reals export Rlist *)
Require Import List.
Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Ring_polynom.
Require Import Ring_tac.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import InitialRing.

Declare ML Module "groebner".

Open Scope R_scope.

Lemma psos_r1b: forall x y, x - y = 0 -> x = y.
intros x y H; replace x with ((x - y) + y);  
  [rewrite H | idtac]; ring.
Qed.

Lemma psos_r1: forall x y, x = y -> x - y = 0.
intros x y H; rewrite H; ring.
Qed.

Ltac equalities_to_goal := 
  match goal with 
|  H: (@eq R ?x 0) |- _ =>
        try generalize H; clear H
|  H: (@eq R 0 ?x) |- _ =>
        try generalize (sym_equal H); clear H
|  H: (@eq R ?x ?y) |- _ =>
        try generalize (psos_r1 _ _ H); clear H
 end.

Lemma groebnerR_not1: forall x y:R, x<>y -> exists z:R, z*(x-y)-1=0.
intros.
exists (1/(x-y)).
field.
unfold not.
unfold not in H.
intros.
apply H.
replace x with ((x-y)+y).
rewrite H0.
ring.
ring.
Qed.

Lemma groebnerR_not1_0: forall x:R, x<>0 -> exists z:R, z*x-1=0.
intros.
exists (1/(x)).
field.
auto.
Qed.

Lemma groebnerR_not2: 1<>0.
auto with *.
Qed.

Lemma groebnerR_diff: forall x y:R, x<>y -> x-y<>0.
Admitted.

(* Removes x<>0 from hypothesis *)
Ltac groebnerR_not_hyp:=
 match goal with 
 | H: ?x<>?y |- _ =>
  match y with
   |0 => 
     let H1:=fresh "Hgroebner" in
     let y:=fresh "x" in
     destruct (@groebnerR_not1_0 _ H) as (y,H1); clear H
   |_ => generalize (@groebnerR_diff _ _ H); clear H; intro
  end
 end.

Ltac groebnerR_not_goal :=
 match goal with
 | |- ?x<>?y => red; intro; apply groebnerR_not2
 | |- False => apply groebnerR_not2
 end.

Ltac groebnerR_begin :=
  intros;
  repeat groebnerR_not_hyp;
  try groebnerR_not_goal;
  try apply psos_r1b;
  repeat equalities_to_goal.

(* code de Benjamin *)

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
  (Pphi 0%R Rplus Rmult (gen_phiZ 0%R 1%R Rplus Rmult Ropp)).

Definition PEevalR : list R -> PEZ -> R := 
   PEeval 0%R Rplus Rmult Rminus Ropp (gen_phiZ 0%R 1%R Rplus Rmult Ropp)
         Nnat.nat_of_N pow.

Lemma P0Z_correct : forall l, PhiR l P0Z = 0%R.
Proof. trivial. Qed.


Lemma PolZadd_correct : forall P' P l,
  PhiR l (PolZadd P P') = (PhiR l P + PhiR l P')%R.
Proof.
 refine (Padd_ok Rset Rext (Rth_ARth Rset Rext (F_R Rfield))
           (gen_phiZ_morph Rset Rext (F_R Rfield))).
Qed.

Lemma PolZmul_correct : forall P P' l,
  PhiR l (PolZmul P P') = (PhiR l P * PhiR l P')%R.
Proof.
 refine (Pmul_ok Rset Rext (Rth_ARth Rset Rext (F_R Rfield))
           (gen_phiZ_morph Rset Rext (F_R Rfield))).
Qed.

Lemma norm_correct :
  forall (l : list R) (pe : PEZ), PEevalR l pe = PhiR l (norm pe).
Proof.
 intros;apply (norm_aux_spec Rset Rext (Rth_ARth Rset Rext (F_R Rfield))
           (gen_phiZ_morph Rset Rext (F_R Rfield)) R_power_theory) with (lmp:= List.nil).
 compute;trivial.
Qed.

Lemma PolZeq_correct : forall P P' l,
  PolZeq P P' = true -> 
  PhiR l P = PhiR l P'.
Proof.
 intros;apply 
   (Peq_ok Rset Rext (gen_phiZ_morph Rset Rext (F_R Rfield)));trivial.
Qed.

Fixpoint Cond0 (A:Type) (Interp:A->R) (l:list A) : Prop :=
  match l with 
  | List.nil => True
  | a::l => Interp a = 0%R /\ Cond0 A Interp l
  end.

Lemma mult_l_correct : forall l la lp, 
  Cond0 PolZ (PhiR l) lp ->
  PhiR l (mult_l la lp) = 0%R.
Proof.
 induction la;simpl;intros;trivial.
 destruct lp;trivial.
 simpl in H;destruct H.
 rewrite PolZadd_correct, PolZmul_correct, H, IHla;[ring | trivial].
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
    PEevalR l qe = 0%R.
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

(* fin du code de Benjamin *)

Lemma groebnerR_l3:forall c p:R, ~c=0 -> c*p=0 -> p=0.
intros.
elim (Rmult_integral _ _ H0);intros.
absurd (c=0);auto.
 auto.
Qed.

Ltac generalise_eq_hyps:=
  repeat
    (match goal with
     |h : (?p = ?q)|- _ => revert h
     end).
  
Ltac lpol_goal t :=
  match t with
  | ?a = 0 -> ?b => 
    let r:= lpol_goal b in
    constr:(a::r)
  | ?a = 0 => constr:(a::nil)
 end.

Fixpoint IPR p {struct p}: R :=
  match p with
    xH => 1
  | xO xH => 1 + 1
  | xO p1 => 2 * (IPR p1)
  | xI xH => 1 + (1 + 1)
  | xI p1 => 1 + 2 * (IPR p1)
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
       let v1  := interpret3 t1 fv in v1 ^(Nnat.nat_of_N t2)
  | (PEc t1) => (IZR1 t1)
  | (PEX n) => List.nth (pred (nat_of_P n)) fv 0
  end.

Ltac AddFvTail2 a l :=
 match l with
 | (@nil _)          => constr:(cons a l)
 | (cons a _)   => l
 | (cons ?x ?l) => let l' := AddFvTail2 a l in constr:(cons x l')
 end.

(* lp est incluse dans fv. La met en tete. *)

Ltac parametres_en_tete fv lp :=
    match fv with
     | (@nil _)        => lp
     | (@cons _ ?x ?fv1) => 
       let res := AddFvTail2 x lp in
         parametres_en_tete fv1 res
    end.

Ltac append1 a l :=
 match l with
 | (@nil _)          => constr:(cons a l)
 | (cons ?x ?l) => let l' := append1 a l in constr:(cons x l')
 end.

Ltac rev l :=
  match l with
   |(@nil _)          => l
   | (cons ?x ?l) => let l' := rev l in append1 x l'
  end.

(* Pompe sur Ring *)

Ltac groebnerR_gen2 Cst_tac CstPow_tac lemma1 req n lH :=
  let Main lhs rhs R radd rmul rsub ropp rpow C :=
    let mkFV := FV Cst_tac CstPow_tac radd rmul rsub ropp rpow in
    let mkPol := mkPolexpr C Cst_tac CstPow_tac radd rmul rsub ropp rpow in
  match goal with
  | Hparam: (@eq (@prod (@List.list ?R) (@List.list ?R)) 
                 (?lparam, ?lvar)
                 ?lparam2) |- _ =>
    clear Hparam;
    generalise_eq_hyps;
    match goal with 
      | |- ?t => 
    let lpol:=lpol_goal t in
    let rec fv_rec l lv:=
      match l with
       |?a::?l1 => 
          let lv1 := mkFV a lv in
          fv_rec l1 lv1 
       | nil => lv
      end in
    let fv := 
       match lvar with
         | (@nil _) => let fv1 := FV_hypo_tac mkFV req lH in
                  let fv1 := fv_rec lpol fv1 in
                  rev fv1
       (* heuristique: les dernieres variables auront le poid le plus fort *)
         | _ => lvar
      end in
    (*let fv1 := FV_hypo_tac mkFV req lH in
    let fv := fv_rec lpol fv1 in*)
    check_fv fv;
    (*idtac "variables:";idtac fv;*)
    let nparam := eval compute in (Z_of_nat (List.length lparam)) in
    let fv := parametres_en_tete fv lparam in
   (* idtac "variables:"; idtac fv;
    idtac "nparam:"; idtac nparam;*)
    let rec mkPol_list lp:=
       match lp with
        |?p::?lp1 => 
            let r := mkPol p fv in
            let lr := mkPol_list lp1 in
            constr:(r::lr)
        | nil =>  constr:(@nil (@PExpr Z))
       end
    in 
    let lpol := mkPol_list lpol in
    let lpol := eval compute in (List.rev lpol) in
    let lpol := constr:((@PEc Z nparam)::lpol) in
    (*idtac lpol;*)
    groebner_compute lpol;
    match goal with
      | |- ?res=?res1 -> _ =>
    let a1:= eval compute in lpol in
    match a1 with
     | ?np::?p2::?lp2 => 
    match res with
     | (?p ::?lp0)::(?c::?lq)::?lci => 
       set (lci1:=lci);
       set (lq1:=lq);
       set (p21:=p2) ;
       let q:= constr:(PEmul c p21) in 
       set (q1:=q);
       set (lp21:=lp2);
       let Hg := fresh "Hg" in 
     assert (Hg:check lp21 q1 (lci1,lq1) = true);
     [vm_compute;trivial
     |intros;
      let Hg2 := fresh "Hg" in
      assert (Hg2:(interpret3 q1 fv)=0);
       [simpl; apply (@check_correct fv lp21 q1 (lci1,lq1) Hg); simpl;
        repeat (match goal with h:_=0%R |- _ => rewrite h end);
        repeat split; auto
       |simpl in Hg2; simpl;
        apply groebnerR_l3 with (interpret3 c fv);simpl;
        [discrR; let Hc := fresh "Hg" in
                 unfold not; intro Hc; ring_simplify in Hc;
                 generalize Hc; clear Hc
        |auto]
       ]
     ] 
    end 
    end 
    end 
  end
 end
  in
  ParseRingComponents lemma1 ltac:(OnEquation req Main)
  .

Ltac groebnerR_gen
  req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post lH rl :=
  pre();groebnerR_gen2 cst_tac pow_tac lemma1 req ring_subst_niter lH .

Ltac groebnerRpv lparam lvar:=
  groebnerR_begin;
  intros;
  generalize (refl_equal (lparam,lvar)); intro;
  let G := Get_goal in
  ring_lookup groebnerR_gen [] G.

Ltac groebnerR := groebnerRpv (@nil R) (@nil R).

Ltac groebnerRp lparam := groebnerRpv lparam (@nil R).


(*************** Examples *)
(*
Open Scope R_scope.
Goal forall x y,
  x+y=0 -> 
  x*y=0 ->
  x^2=0.
Time groebnerR.
Qed.

Goal forall x y z u v,
  x+y+z+u+v=0 -> 
  x*y+x*z+x*u+x*v+y*z+y*u+y*v+z*u+z*v+u*v=0->
  x*y*z+x*y*u+x*y*v+x*z*u+x*z*v+x*u*v+y*z*u+y*z*v+y*u*v+z*u*v=0->
  x*y*z*u+y*z*u*v+z*u*v*x+u*v*x*y+v*x*y*z=0 ->
  x*y*z*u*v=0 -> x^5=0.
Time groebnerR.
Qed.
*)















