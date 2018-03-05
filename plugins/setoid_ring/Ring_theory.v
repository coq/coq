(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Setoid Morphisms BinPos BinNat.

Set Implicit Arguments.

Module RingSyntax.
Reserved Notation "x ?=! y" (at level 70, no associativity).
Reserved Notation "x +! y " (at level 50, left associativity).
Reserved Notation "x -! y" (at level 50, left associativity).
Reserved Notation "x *! y" (at level 40, left associativity).
Reserved Notation "-! x" (at level 35, right associativity).

Reserved Notation "[ x ]" (at level 0).

Reserved Notation "x ?== y" (at level 70, no associativity).
Reserved Notation "x -- y" (at level 50, left associativity).
Reserved Notation "x ** y" (at level 40, left associativity).
Reserved Notation "-- x" (at level 35, right associativity).

Reserved Notation "x == y" (at level 70, no associativity).
End RingSyntax.
Import RingSyntax.

(* Set Universe Polymorphism. *)

Section Power.
 Variable R:Type.
 Variable rI : R.
 Variable rmul : R -> R -> R.
 Variable req : R -> R -> Prop.
 Variable Rsth : Equivalence req.
 Infix "*" := rmul.
 Infix "==" := req.

 Hypothesis mul_ext : Proper (req ==> req ==> req) rmul.
 Hypothesis mul_assoc  : forall x y z, x * (y * z) == (x * y) * z.

 Fixpoint pow_pos (x:R) (i:positive) : R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos x i in p * p
  | xI i => let p := pow_pos x i in x * (p * p)
  end.

 Lemma pow_pos_swap x j : pow_pos x j * x == x * pow_pos x j.
 Proof.
  induction j; simpl; rewrite <- ?mul_assoc.
  - f_equiv. now do 2 (rewrite IHj, mul_assoc).
  - now do 2 (rewrite IHj, mul_assoc).
  - reflexivity.
 Qed.

 Lemma pow_pos_succ x j :
   pow_pos x (Pos.succ j) == x * pow_pos x j.
 Proof.
  induction j; simpl; try reflexivity.
  rewrite IHj, <- mul_assoc; f_equiv.
  now rewrite mul_assoc, pow_pos_swap, mul_assoc.
 Qed.

 Lemma pow_pos_add x i j :
   pow_pos x (i + j) == pow_pos x i * pow_pos x j.
 Proof.
  induction i using Pos.peano_ind.
  - now rewrite Pos.add_1_l, pow_pos_succ.
  - now rewrite Pos.add_succ_l, !pow_pos_succ, IHi, mul_assoc.
 Qed.

 Definition pow_N (x:R) (p:N) :=
  match p with
  | N0 => rI
  | Npos p => pow_pos x p
  end.

 Definition id_phi_N (x:N) : N := x.

 Lemma pow_N_pow_N x n : pow_N x (id_phi_N n) == pow_N x n.
 Proof.
  reflexivity.
 Qed.

End Power.

Section DEFINITIONS.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop.
 Notation "0" := rO.  Notation "1" := rI.
 Infix "==" := req. Infix "+" := radd. Infix "*" := rmul.
 Infix "-" := rsub. Notation "- x" := (ropp x).

 (** Semi Ring *)
 Record semi_ring_theory : Prop := mk_srt {
    SRadd_0_l   : forall n, 0 + n == n;
    SRadd_comm  : forall n m, n + m == m + n ;
    SRadd_assoc : forall n m p, n + (m + p) == (n + m) + p;
    SRmul_1_l   : forall n, 1*n == n;
    SRmul_0_l   : forall n, 0*n == 0;
    SRmul_comm  : forall n m, n*m == m*n;
    SRmul_assoc : forall n m p, n*(m*p) == (n*m)*p;
    SRdistr_l   : forall n m p, (n + m)*p == n*p + m*p
  }.

 (** Almost Ring *)
(*Almost ring are no ring : Ropp_def is missing **)
 Record almost_ring_theory : Prop := mk_art {
    ARadd_0_l   : forall x, 0 + x == x;
    ARadd_comm  : forall x y, x + y == y + x;
    ARadd_assoc : forall x y z, x + (y + z) == (x + y) + z;
    ARmul_1_l   : forall x, 1 * x == x;
    ARmul_0_l   : forall x, 0 * x == 0;
    ARmul_comm  : forall x y, x * y == y * x;
    ARmul_assoc : forall x y z, x * (y * z) == (x * y) * z;
    ARdistr_l   : forall x y z, (x + y) * z == (x * z) + (y * z);
    ARopp_mul_l : forall x y, -(x * y) == -x * y;
    ARopp_add   : forall x y, -(x + y) == -x + -y;
    ARsub_def   : forall x y, x - y == x + -y
  }.

 (** Ring *)
 Record ring_theory : Prop := mk_rt {
    Radd_0_l    : forall x, 0 + x == x;
    Radd_comm   : forall x y, x + y == y + x;
    Radd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
    Rmul_1_l    : forall x, 1 * x == x;
    Rmul_comm   : forall x y, x * y == y * x;
    Rmul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
    Rdistr_l    : forall x y z, (x + y) * z == (x * z) + (y * z);
    Rsub_def    : forall x y, x - y == x + -y;
    Ropp_def    : forall x, x + (- x) == 0
 }.

 (** Equality is extensional *)

 Record sring_eq_ext : Prop := mk_seqe {
    (* SRing operators are compatible with equality *)
    SRadd_ext : Proper (req ==> req ==> req) radd;
    SRmul_ext : Proper (req ==> req ==> req) rmul
  }.

 Record ring_eq_ext : Prop := mk_reqe {
    (* Ring operators are compatible with equality *)
    Radd_ext : Proper (req ==> req ==> req) radd;
    Rmul_ext : Proper (req ==> req ==> req) rmul;
    Ropp_ext : Proper (req ==> req) ropp
  }.

 (** Interpretation morphisms definition*)
 Section MORPHISM.
 Variable C:Type.
 Variable (cO cI : C) (cadd cmul csub : C->C->C) (copp : C->C).
 Variable ceqb : C->C->bool.
 (* [phi] est un morphisme de [C] dans [R] *)
 Variable phi : C -> R.
 Infix "+!" := cadd. Infix "-!" := csub.
 Infix "*!" := cmul. Notation "-! x" := (copp x).
 Infix "?=!" := ceqb. Notation "[ x ]" := (phi x).

(*for semi rings*)
 Record semi_morph : Prop := mkRmorph {
    Smorph0 : [cO] == 0;
    Smorph1 : [cI] == 1;
    Smorph_add : forall x y, [x +! y] == [x]+[y];
    Smorph_mul : forall x y, [x *! y] == [x]*[y];
    Smorph_eq  : forall x y, x?=!y = true -> [x] == [y]
  }.

(* for rings*)
 Record ring_morph : Prop := mkmorph {
    morph0    : [cO] == 0;
    morph1    : [cI] == 1;
    morph_add : forall x y, [x +! y] == [x]+[y];
    morph_sub : forall x y, [x -! y] == [x]-[y];
    morph_mul : forall x y, [x *! y] == [x]*[y];
    morph_opp : forall x, [-!x] == -[x];
    morph_eq  : forall x y, x?=!y = true -> [x] == [y]
  }.

 Section SIGN.
  Variable get_sign : C -> option C.
  Record sign_theory : Prop := mksign_th {
    sign_spec : forall c c', get_sign c = Some c' -> c ?=! -! c' = true
  }.
 End SIGN.

 Definition get_sign_None (c:C) := @None C.

 Lemma get_sign_None_th : sign_theory get_sign_None.
 Proof. constructor;intros;discriminate. Qed.

 Section DIV.
  Variable cdiv: C -> C -> C*C.
  Record div_theory : Prop := mkdiv_th {
    div_eucl_th : forall a b, let (q,r) := cdiv a b in [a] == [b *! q +! r]
  }.
 End DIV.

 End MORPHISM.

 (** Identity is a morphism *)
 Variable Rsth : Equivalence req.
 Variable reqb : R->R->bool.
 Hypothesis morph_req : forall x y, (reqb x y) = true -> x == y.
 Definition IDphi (x:R) := x.
 Lemma IDmorph : ring_morph rO rI radd rmul rsub ropp reqb IDphi.
 Proof.
  now apply (mkmorph rO rI radd rmul rsub ropp reqb IDphi).
 Qed.

 (** Specification of the power function *)
 Section POWER.
  Variable Cpow : Type.
  Variable Cp_phi : N -> Cpow.
  Variable rpow : R -> Cpow -> R.

  Record power_theory : Prop := mkpow_th {
    rpow_pow_N : forall r n, req (rpow r (Cp_phi n)) (pow_N rI rmul r n)
  }.

 End POWER.

 Definition pow_N_th :=
   mkpow_th id_phi_N (pow_N rI rmul) (pow_N_pow_N rI rmul Rsth).


End DEFINITIONS.

Section ALMOST_RING.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop.
 Notation "0" := rO.  Notation "1" := rI.
 Infix "==" := req. Infix "+" := radd.  Infix "* " := rmul.

 (** Leibniz equality leads to a setoid theory and is extensional*)
 Lemma Eqsth : Equivalence (@eq R).
 Proof. exact eq_equivalence. Qed.

 Lemma Eq_s_ext : sring_eq_ext radd rmul (@eq R).
 Proof. constructor;solve_proper. Qed.

 Lemma Eq_ext : ring_eq_ext radd rmul ropp (@eq R).
 Proof. constructor;solve_proper. Qed.

 Variable Rsth : Equivalence req.

 Section SEMI_RING.
 Variable SReqe : sring_eq_ext radd rmul req.

   Add Morphism radd with signature (req ==> req ==> req) as radd_ext1.
   Proof. exact (SRadd_ext SReqe). Qed.

   Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext1.
   Proof. exact (SRmul_ext SReqe). Qed.

 Variable SRth : semi_ring_theory 0 1 radd rmul req.

 (** Every semi ring can be seen as an almost ring, by taking :
        [-x = x] and [x - y = x + y] *)
 Definition SRopp (x:R) := x. Notation "- x" := (SRopp x).

 Definition SRsub x y := x + -y. Infix "-" := SRsub.

 Lemma SRopp_ext : forall x y, x == y -> -x == -y.
 Proof. intros x y H; exact H. Qed.

 Lemma SReqe_Reqe : ring_eq_ext radd rmul SRopp req.
 Proof.
  constructor.
  - exact (SRadd_ext SReqe).
  - exact (SRmul_ext SReqe).
  - exact SRopp_ext.
 Qed.

 Lemma SRopp_mul_l : forall x y, -(x * y) == -x * y.
 Proof. reflexivity. Qed.

 Lemma SRopp_add : forall x y, -(x + y) == -x + -y.
 Proof. reflexivity. Qed.

 Lemma SRsub_def   : forall x y, x - y == x + -y.
 Proof. reflexivity. Qed.

 Lemma SRth_ARth : almost_ring_theory 0 1 radd rmul SRsub SRopp req.
 Proof (mk_art 0 1 radd rmul SRsub SRopp req
    (SRadd_0_l SRth) (SRadd_comm SRth) (SRadd_assoc SRth)
    (SRmul_1_l SRth) (SRmul_0_l SRth)
    (SRmul_comm SRth) (SRmul_assoc SRth) (SRdistr_l SRth)
    SRopp_mul_l SRopp_add SRsub_def).

 (** Identity morphism for semi-ring equipped with their almost-ring structure*)
 Variable reqb : R->R->bool.

 Hypothesis morph_req : forall x y, (reqb x y) = true -> x == y.

 Definition SRIDmorph : ring_morph 0 1 radd rmul SRsub SRopp req
                            0 1 radd rmul SRsub SRopp reqb (@IDphi R).
 Proof.
  now apply mkmorph.
 Qed.

 (* a semi_morph can be extended to a ring_morph for the almost_ring derived
    from a semi_ring, provided the ring is a setoid (we only need
    reflexivity) *)
 Variable C : Type.
 Variable (cO cI : C) (cadd cmul: C->C->C).
 Variable (ceqb : C -> C -> bool).
 Variable phi : C -> R.
 Variable Smorph : semi_morph rO rI radd rmul req cO cI cadd cmul ceqb phi.

 Lemma SRmorph_Rmorph :
   ring_morph rO rI radd rmul SRsub SRopp req
              cO cI cadd cmul cadd (fun x => x) ceqb phi.
 Proof.
 case Smorph; now constructor.
 Qed.

 End  SEMI_RING.
 Infix "-" := rsub.
 Notation "- x" := (ropp x).

 Variable Reqe : ring_eq_ext radd rmul ropp req.

   Add Morphism radd with signature (req ==> req ==> req) as radd_ext2.
   Proof. exact (Radd_ext Reqe). Qed.

   Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext2.
   Proof. exact (Rmul_ext Reqe). Qed.

   Add Morphism ropp with signature (req ==> req) as ropp_ext2.
   Proof. exact (Ropp_ext Reqe). Qed.

 Section RING.
 Variable Rth : ring_theory 0 1 radd rmul rsub ropp req.

 (** Rings are almost rings*)
 Lemma Rmul_0_l x : 0 * x == 0.
 Proof.
  setoid_replace (0*x) with ((0+1)*x + -x).
  now rewrite (Radd_0_l Rth), (Rmul_1_l Rth), (Ropp_def Rth).

  rewrite (Rdistr_l Rth), (Rmul_1_l Rth).
  rewrite <- (Radd_assoc Rth), (Ropp_def Rth).
  now rewrite (Radd_comm Rth), (Radd_0_l Rth).
 Qed.

 Lemma Ropp_mul_l x y : -(x * y) == -x * y.
 Proof.
  rewrite <-(Radd_0_l Rth (- x * y)).
  rewrite (Radd_comm Rth), <-(Ropp_def Rth (x*y)).
  rewrite (Radd_assoc Rth), <- (Rdistr_l Rth).
  rewrite (Rth.(Radd_comm) (-x)), (Ropp_def Rth).
  now rewrite Rmul_0_l, (Radd_0_l Rth).
 Qed.

 Lemma Ropp_add x y : -(x + y) == -x + -y.
 Proof.
  rewrite <- ((Radd_0_l Rth) (-(x+y))).
  rewrite <- ((Ropp_def Rth) x).
  rewrite <- ((Radd_0_l Rth) (x + - x + - (x + y))).
  rewrite <- ((Ropp_def Rth) y).
  rewrite ((Radd_comm Rth) x).
  rewrite ((Radd_comm Rth) y).
  rewrite <- ((Radd_assoc Rth) (-y)).
  rewrite <- ((Radd_assoc Rth) (- x)).
  rewrite ((Radd_assoc Rth)  y).
  rewrite ((Radd_comm Rth) y).
  rewrite <- ((Radd_assoc Rth)  (- x)).
  rewrite ((Radd_assoc Rth) y).
  rewrite ((Radd_comm Rth) y), (Ropp_def Rth).
  rewrite ((Radd_comm Rth) (-x) 0), (Radd_0_l Rth).
  now apply (Radd_comm Rth).
 Qed.

 Lemma Ropp_opp x : - -x == x.
 Proof.
  rewrite <- (Radd_0_l Rth (- -x)).
  rewrite <- (Ropp_def Rth x).
  rewrite <- (Radd_assoc Rth), (Ropp_def Rth).
  rewrite ((Radd_comm Rth) x); now apply (Radd_0_l Rth).
 Qed.

 Lemma  Rth_ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.
 Proof
  (mk_art 0 1 radd rmul rsub ropp req (Radd_0_l Rth) (Radd_comm Rth) (Radd_assoc Rth)
    (Rmul_1_l Rth) Rmul_0_l (Rmul_comm Rth) (Rmul_assoc Rth) (Rdistr_l Rth)
    Ropp_mul_l Ropp_add (Rsub_def Rth)).

 (** Every semi morphism between two rings is a morphism*)
 Variable C : Type.
 Variable (cO cI : C) (cadd cmul csub: C->C->C) (copp : C -> C).
 Variable (ceq : C -> C -> Prop) (ceqb : C -> C -> bool).
 Variable phi : C -> R.
  Infix "+!" := cadd. Infix "*!" := cmul.
  Infix "-!" := csub. Notation "-! x" := (copp x).
  Notation "?=!" := ceqb. Notation "[ x ]" := (phi x).
 Variable Csth : Equivalence ceq.
 Variable Ceqe : ring_eq_ext cadd cmul copp ceq.

   Add Parametric Relation : C ceq
     reflexivity  proved by Csth.(@Equivalence_Reflexive _ _)
     symmetry     proved by Csth.(@Equivalence_Symmetric _ _)
     transitivity proved by Csth.(@Equivalence_Transitive _ _)
    as C_setoid.

   Add Morphism cadd with signature (ceq ==> ceq ==> ceq) as cadd_ext.
   Proof. exact (Radd_ext Ceqe). Qed.

   Add Morphism cmul with signature (ceq ==> ceq ==> ceq) as cmul_ext.
   Proof. exact (Rmul_ext Ceqe). Qed.

   Add Morphism copp with signature (ceq ==> ceq) as copp_ext.
   Proof. exact (Ropp_ext Ceqe). Qed.

 Variable Cth : ring_theory cO cI cadd cmul csub copp ceq.
 Variable Smorph : semi_morph 0 1 radd rmul req cO cI cadd cmul ceqb phi.
 Variable phi_ext : forall x y, ceq x y -> [x] == [y].

   Add Morphism phi with signature (ceq ==> req) as phi_ext1.
   Proof. exact phi_ext. Qed.

 Lemma Smorph_opp x : [-!x] == -[x].
 Proof.
  rewrite <-  (Rth.(Radd_0_l) [-!x]).
  rewrite <- ((Ropp_def Rth) [x]).
  rewrite ((Radd_comm Rth) [x]).
  rewrite <- (Radd_assoc Rth).
  rewrite <- (Smorph_add Smorph).
  rewrite (Ropp_def Cth).
  rewrite (Smorph0 Smorph).
  rewrite (Radd_comm Rth (-[x])).
  now apply (Radd_0_l Rth).
 Qed.

 Lemma Smorph_sub x y : [x -! y] == [x] - [y].
 Proof.
  rewrite (Rsub_def Cth), (Rsub_def Rth).
  now rewrite (Smorph_add Smorph), Smorph_opp.
 Qed.

 Lemma Smorph_morph :
   ring_morph 0 1 radd rmul rsub ropp req
     cO cI cadd cmul csub copp ceqb phi.
 Proof
  (mkmorph 0 1 radd rmul rsub ropp req cO cI cadd cmul csub copp ceqb phi
        (Smorph0 Smorph) (Smorph1 Smorph)
         (Smorph_add Smorph) Smorph_sub (Smorph_mul Smorph) Smorph_opp
         (Smorph_eq Smorph)).

 End RING.

 (** Useful lemmas on almost ring *)
 Variable ARth : almost_ring_theory 0 1 radd rmul rsub ropp req.

 Lemma ARth_SRth : semi_ring_theory 0 1 radd rmul req.
Proof.
elim ARth; intros.
constructor; trivial.
Qed.

 Instance ARsub_ext : Proper (req ==> req ==> req) rsub.
 Proof.
  intros x1 x2 Ex y1 y2 Ey.
  now rewrite !(ARsub_def ARth), Ex, Ey.
 Qed.

 Ltac mrewrite :=
   repeat first
     [ rewrite (ARadd_0_l ARth)
     | rewrite <- ((ARadd_comm ARth) 0)
     | rewrite (ARmul_1_l ARth)
     | rewrite <- ((ARmul_comm ARth) 1)
     | rewrite (ARmul_0_l ARth)
     | rewrite <- ((ARmul_comm ARth) 0)
     | rewrite (ARdistr_l ARth)
     | reflexivity
     | match goal with
       | |- context [?z * (?x + ?y)] => rewrite ((ARmul_comm ARth) z (x+y))
       end].

 Lemma ARadd_0_r x : x + 0 == x.
 Proof. mrewrite. Qed.

 Lemma ARmul_1_r x : x * 1 == x.
 Proof. mrewrite. Qed.

 Lemma ARmul_0_r x : x * 0 == 0.
 Proof. mrewrite. Qed.

 Lemma ARdistr_r x y z : z * (x + y) == z*x + z*y.
 Proof.
  mrewrite. now rewrite !(ARth.(ARmul_comm) z).
 Qed.

 Lemma ARadd_assoc1 x y z : (x + y) + z == (y + z) + x.
 Proof.
  now rewrite <-(ARth.(ARadd_assoc) x), (ARth.(ARadd_comm) x).
 Qed.

 Lemma ARadd_assoc2 x y z : (y + x) + z == (y + z) + x.
 Proof.
  now rewrite <- !(ARadd_assoc ARth), ((ARadd_comm ARth) x).
 Qed.

 Lemma ARmul_assoc1 x y z : (x * y) * z == (y * z) * x.
 Proof.
  now rewrite <- ((ARmul_assoc ARth) x), ((ARmul_comm ARth) x).
 Qed.

 Lemma ARmul_assoc2 x y z : (y * x) * z == (y * z) * x.
 Proof.
  now rewrite <- !(ARmul_assoc ARth), ((ARmul_comm ARth) x).
 Qed.

 Lemma ARopp_mul_r x y : - (x * y) == x * -y.
 Proof.
  rewrite ((ARmul_comm ARth) x y), (ARopp_mul_l ARth).
  now apply (ARmul_comm ARth).
 Qed.

 Lemma ARopp_zero : -0 == 0.
 Proof.
  now rewrite <- (ARmul_0_r 0), (ARopp_mul_l ARth), !ARmul_0_r.
 Qed.

End ALMOST_RING.

Section AddRing.

(* Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop. *)

Inductive ring_kind : Type :=
| Abstract
| Computational
    (R:Type)
    (req : R -> R -> Prop)
    (reqb : R -> R -> bool)
    (_ : forall x y, (reqb x y) = true -> req x y)
| Morphism
    (R : Type)
    (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R)
    (req : R -> R -> Prop)
    (C : Type)
    (cO cI : C) (cadd cmul csub : C->C->C) (copp : C->C)
    (ceqb : C->C->bool)
    phi
    (_ : ring_morph rO rI radd rmul rsub ropp req
                    cO cI cadd cmul csub copp ceqb phi).

End AddRing.


(** Some simplification tactics*)
Ltac gen_reflexivity Rsth := apply (Seq_refl _ _ Rsth).

Ltac gen_srewrite Rsth Reqe ARth :=
  repeat first
     [ gen_reflexivity Rsth
     | progress rewrite (ARopp_zero Rsth Reqe ARth)
     | rewrite (ARadd_0_l ARth)
     | rewrite (ARadd_0_r Rsth ARth)
     | rewrite (ARmul_1_l ARth)
     | rewrite (ARmul_1_r Rsth ARth)
     | rewrite (ARmul_0_l ARth)
     | rewrite (ARmul_0_r Rsth ARth)
     | rewrite (ARdistr_l ARth)
     | rewrite (ARdistr_r Rsth Reqe ARth)
     | rewrite (ARadd_assoc ARth)
     | rewrite (ARmul_assoc ARth)
     | progress rewrite (ARopp_add ARth)
     | progress rewrite (ARsub_def ARth)
     | progress rewrite <- (ARopp_mul_l ARth)
     | progress rewrite <- (ARopp_mul_r Rsth Reqe ARth) ].

Ltac gen_srewrite_sr Rsth Reqe ARth :=
  repeat first
     [ gen_reflexivity Rsth
     | progress rewrite (ARopp_zero Rsth Reqe ARth)
     | rewrite (ARadd_0_l ARth)
     | rewrite (ARadd_0_r Rsth ARth)
     | rewrite (ARmul_1_l ARth)
     | rewrite (ARmul_1_r Rsth ARth)
     | rewrite (ARmul_0_l ARth)
     | rewrite (ARmul_0_r Rsth ARth)
     | rewrite (ARdistr_l ARth)
     | rewrite (ARdistr_r Rsth Reqe ARth)
     | rewrite (ARadd_assoc ARth)
     | rewrite (ARmul_assoc ARth) ].

Ltac gen_add_push add Rsth Reqe ARth x :=
  repeat (match goal with
  | |- context [add (add ?y x) ?z] =>
     progress rewrite (ARadd_assoc2 Rsth Reqe ARth x y z)
  | |- context [add (add x ?y) ?z] =>
     progress rewrite (ARadd_assoc1 Rsth ARth x y z)
  | |- context [(add x ?y)] =>
     progress rewrite (ARadd_comm ARth x y)
  end).

Ltac gen_mul_push mul Rsth Reqe ARth x :=
  repeat (match goal with
  | |- context [mul (mul ?y x) ?z] =>
     progress rewrite (ARmul_assoc2 Rsth Reqe ARth x y z)
  | |- context [mul (mul x ?y) ?z] =>
     progress rewrite (ARmul_assoc1 Rsth ARth x y z)
  | |- context [(mul x ?y)] =>
     progress rewrite (ARmul_comm ARth x y)
  end).
