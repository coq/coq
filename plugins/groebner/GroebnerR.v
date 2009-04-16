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

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Import RealField Rdefinitions Rfunctions RIneq DiscrR.
Require Import Ring_polynom Ring_tac InitialRing.

Declare ML Module "groebner_plugin".

Local Open Scope R_scope.

Lemma psos_r1b: forall x y, x - y = 0 -> x = y.
intros x y H; replace x with ((x - y) + y);  
  [rewrite H | idtac]; ring.
Qed.

Lemma psos_r1: forall x y, x = y -> x - y = 0.
intros x y H; rewrite H; ring.
Qed.

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


Ltac equalities_to_goal := 
  lazymatch goal with 
  |  H: (@eq R ?x 0) |- _ => try revert H
  |  H: (@eq R 0 ?x) |- _ =>
          try generalize (sym_equal H); clear H
  |  H: (@eq R ?x ?y) |- _ =>
          try generalize (psos_r1 _ _ H); clear H
   end.

Lemma groebnerR_not2: 1<>0.
auto with *.
Qed.

Lemma groebnerR_diff: forall x y:R, x<>y -> x-y<>0.
intros.
intro; apply H.
replace x with (x-y+y) by ring.
rewrite H0; ring.
Qed.

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
 | |- ?x<>?y :> R => red; intro; apply groebnerR_not2
 | |- False       => apply groebnerR_not2
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
  (Pphi 0 Rplus Rmult (gen_phiZ 0 1 Rplus Rmult Ropp)).

Definition PEevalR : list R -> PEZ -> R := 
   PEeval 0 Rplus Rmult Rminus Ropp (gen_phiZ 0 1 Rplus Rmult Ropp)
         Nnat.nat_of_N pow.

Lemma P0Z_correct : forall l, PhiR l P0Z = 0.
Proof. trivial. Qed.


Lemma PolZadd_correct : forall P' P l,
  PhiR l (PolZadd P P') = (PhiR l P + PhiR l P').
Proof.
 refine (Padd_ok Rset Rext (Rth_ARth Rset Rext (F_R Rfield))
           (gen_phiZ_morph Rset Rext (F_R Rfield))).
Qed.

Lemma PolZmul_correct : forall P P' l,
  PhiR l (PolZmul P P') = (PhiR l P * PhiR l P').
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
  | a::l => Interp a = 0 /\ Cond0 A Interp l
  end.

Lemma mult_l_correct : forall l la lp, 
  Cond0 PolZ (PhiR l) lp ->
  PhiR l (mult_l la lp) = 0.
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
    PEevalR l qe = 0.
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

Lemma groebnerR_l3:forall c p r, ~c=0 -> c*p^r=0 -> p=0.
intros.
elim (Rmult_integral _ _ H0);intros.
 absurd (c=0);auto.

 clear H0; induction r; simpl in *.
  contradict H1; discrR. 

  elim (Rmult_integral _ _ H1); auto.
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


Ltac groebner_call_n nparam p rr lp kont :=
  groebner_compute (PEc nparam :: PEpow p rr :: lp);
  match goal with
  | |- (?c::PEpow _ ?r::?lq0)::?lci0 = _ -> _ =>
    intros _;
    set (lci:=lci0);
    set (lq:=lq0);
    kont c rr lq lci
  end.

Ltac groebner_call nparam p lp kont :=
  let rec try_n n :=
    lazymatch n with
    | 6%N => fail
    | _ =>
(*        idtac "Trying power: " n;*)
        groebner_call_n nparam p n lp kont ||
        let n' := eval compute in (Nsucc n) in try_n n'
    end in
  try_n 1%N. 


Ltac groebnerR_gen lparam lvar n RNG lH _rl :=
  get_Pre RNG ();
  let mkFV := Ring_tac.get_RingFV RNG in
  let mkPol := Ring_tac.get_RingMeta RNG in
  generalise_eq_hyps;
  let t := Get_goal in
  let lpol := lpol_goal t in
  intros;
  let fv := 
    match lvar with
    | nil =>
        let fv1 := FV_hypo_tac mkFV ltac:(get_Eq RNG) lH in
        let fv1 := list_fold_right mkFV fv1 lpol in
        rev fv1
    (* heuristique: les dernieres variables auront le poid le plus fort *)
    | _ => lvar
    end in
  check_fv fv;
  (*idtac "variables:";idtac fv;*)
  let nparam := eval compute in (Z_of_nat (List.length lparam)) in
  let fv := parametres_en_tete fv lparam in
 (* idtac "variables:"; idtac fv;
    idtac "nparam:"; idtac nparam;*)
  let lpol := list_fold_right
    ltac:(fun p l => let p' := mkPol p fv in constr:(p'::l))
    (@nil (PExpr Z))
    lpol in
  let lpol := eval compute in (List.rev lpol) in
  (*idtac lpol;*)
  let SplitPolyList kont :=
    match lpol with
    | ?p2::?lp2 => kont p2 lp2
    end in
  SplitPolyList ltac:(fun p lp =>
    set (p21:=p) ;
    set (lp21:=lp);
    groebner_call nparam p lp ltac:(fun c r lq lci =>
      set (q := PEmul c (PEpow p21 r));
      let Hg := fresh "Hg" in 
      assert (Hg:check lp21 q (lci,lq) = true);
      [ (vm_compute;reflexivity) || idtac "invalid groebner certificate"
      | let Hg2 := fresh "Hg" in
        assert (Hg2: interpret3 q fv = 0);
        [ simpl; apply (@check_correct fv lp21 q (lci,lq) Hg); simpl;
          repeat (split;[assumption|idtac]); exact I
        | simpl in Hg2; simpl;
          apply groebnerR_l3 with (interpret3 c fv) (Nnat.nat_of_N r);simpl;
          [ discrR || idtac "could not prove discrimination result"
          | exact Hg2]
        ]
      ])).

Ltac groebnerRpv lparam lvar:=
  groebnerR_begin;
  intros;
  let G := Get_goal in
  ring_lookup
    (PackRing ltac:(groebnerR_gen lparam lvar ring_subst_niter))
    [] G.

Ltac groebnerR := groebnerRpv (@nil R) (@nil R).

Ltac groebnerRp lparam := groebnerRpv lparam (@nil R).


(*************** Examples *)
(*
Section Examples.

Require Import List Ring_polynom.
Delimit Scope PE_scope with PE.
Infix "+" := PEadd : PE_scope.
Infix "*" := PEmul : PE_scope.
Infix "-" := PEsub : PE_scope.
Infix "^" := PEpow : PE_scope.
Notation "[ n ]" := (@PEc Z n) (at level 0).

Open Scope R_scope.

Goal forall x y,
  x+y=0 -> 
  x*y=0 ->
  x^2=0.
groebnerR.
Qed.

Goal forall x, x^2=0 -> x=0.
groebnerR.
Qed.

(*
Notation X  := (PEX Z 3).
Notation Y  := (PEX Z 2).
Notation Z_ := (PEX Z 1).
*)
Goal forall x y z,
  x+y+z=0 -> 
  x*y+x*z+y*z=0->
  x*y*z=0 -> x^3=0.
Time groebnerR.
Qed.

(*
Notation X  := (PEX Z 4).
Notation Y  := (PEX Z 3).
Notation Z_ := (PEX Z 2).
Notation U  := (PEX Z 1).
*)
Goal forall x y z u,
  x+y+z+u=0 -> 
  x*y+x*z+x*u+y*z+y*u+z*u=0->
  x*y*z+x*y*u+x*z*u+y*z*u=0->
  x*y*z*u=0 -> x^4=0.
Time groebnerR.
Qed.

(*
Notation x_ := (PEX Z 5).
Notation y_ := (PEX Z 4).
Notation z_ := (PEX Z 3).
Notation u_ := (PEX Z 2).
Notation v_ := (PEX Z 1).
Notation "x :: y" := (List.cons x y)
(at level 60, right associativity, format "'[hv' x  ::  '/' y ']'").
Notation "x :: y" := (List.app x y)
(at level 60, right associativity, format "x :: y").
*)

Goal forall x y z u v,
  x+y+z+u+v=0 -> 
  x*y+x*z+x*u+x*v+y*z+y*u+y*v+z*u+z*v+u*v=0->
  x*y*z+x*y*u+x*y*v+x*z*u+x*z*v+x*u*v+y*z*u+y*z*v+y*u*v+z*u*v=0->
  x*y*z*u+y*z*u*v+z*u*v*x+u*v*x*y+v*x*y*z=0 ->
  x*y*z*u*v=0 -> x^5=0.
Time groebnerR.
Qed.

End Examples.
*)












