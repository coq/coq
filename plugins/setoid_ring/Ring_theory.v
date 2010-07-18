(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Setoid.
Require Import BinPos.
Require Import BinNat.
Import Morphisms. (* For Hints *)

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

Section Power.
 Variable R:Type.
 Variable rI : R.
 Variable rmul : R -> R -> R.
 Variable req : R -> R -> Prop.
 Variable Rsth : Setoid_Theory R req.
 Notation "x * y " := (rmul x y).
 Notation "x == y" := (req x y).

 Hypothesis mul_ext :
   forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 * y1 == x2 * y2.
 Hypothesis mul_comm : forall x y, x * y == y * x.
 Hypothesis mul_assoc  : forall x y z, x * (y * z) == (x * y) * z.
 Add Setoid R req Rsth as R_set_Power.
 Add Morphism rmul : rmul_ext_Power. exact mul_ext. Qed.


 Fixpoint pow_pos (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos x i in rmul p p
  | xI i => let p := pow_pos x i in rmul x (rmul p p)
  end.

 Lemma pow_pos_Psucc : forall x j, pow_pos x (Psucc j) == x * pow_pos x j.
 Proof.
  induction j;simpl.
  rewrite IHj.
  rewrite (mul_comm x (pow_pos x j *pow_pos x j)).
  setoid_rewrite (mul_comm x (pow_pos x j)) at 2.
  repeat rewrite mul_assoc. apply (Seq_refl _ _ Rsth).
  repeat rewrite mul_assoc. apply (Seq_refl _ _ Rsth).
  apply (Seq_refl _ _ Rsth).
 Qed.

 Lemma pow_pos_Pplus : forall x i j, pow_pos x (i + j) == pow_pos x i * pow_pos x j.
 Proof.
  intro x;induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite pow_pos_Psucc.
  simpl;repeat rewrite mul_assoc. apply (Seq_refl _ _ Rsth).
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi;rewrite mul_assoc. apply (Seq_refl _ _ Rsth).
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite pow_pos_Psucc;
   simpl. apply (Seq_refl _ _ Rsth).
 Qed.

 Definition pow_N (x:R) (p:N) :=
  match p with
  | N0 => rI
  | Npos p => pow_pos x p
  end.

 Definition id_phi_N (x:N) : N := x.

 Lemma pow_N_pow_N : forall x n, pow_N x (id_phi_N n) == pow_N x n.
 Proof.
  intros; apply (Seq_refl _ _ Rsth).
 Qed.

End Power.

Section DEFINITIONS.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x == y" := (req x y).

 (** Semi Ring *)
 Record semi_ring_theory : Prop := mk_srt {
    SRadd_0_l   : forall n, 0 + n == n;
    SRadd_comm   : forall n m, n + m == m + n ;
    SRadd_assoc : forall n m p, n + (m + p) == (n + m) + p;
    SRmul_1_l   : forall n, 1*n == n;
    SRmul_0_l   : forall n, 0*n == 0;
    SRmul_comm   : forall n m, n*m == m*n;
    SRmul_assoc : forall n m p, n*(m*p) == (n*m)*p;
    SRdistr_l   : forall n m p, (n + m)*p == n*p + m*p
  }.

 (** Almost Ring *)
(*Almost ring are no ring : Ropp_def is missing **)
 Record almost_ring_theory : Prop := mk_art {
    ARadd_0_l   : forall x, 0 + x == x;
    ARadd_comm   : forall x y, x + y == y + x;
    ARadd_assoc : forall x y z, x + (y + z) == (x + y) + z;
    ARmul_1_l   : forall x, 1 * x == x;
    ARmul_0_l   : forall x, 0 * x == 0;
    ARmul_comm   : forall x y, x * y == y * x;
    ARmul_assoc : forall x y z, x * (y * z) == (x * y) * z;
    ARdistr_l   : forall x y z, (x + y) * z == (x * z) + (y * z);
    ARopp_mul_l : forall x y, -(x * y) == -x * y;
    ARopp_add   : forall x y, -(x + y) == -x + -y;
    ARsub_def   : forall x y, x - y == x + -y
  }.

 (** Ring *)
 Record ring_theory : Prop := mk_rt {
    Radd_0_l    : forall x, 0 + x == x;
    Radd_comm    : forall x y, x + y == y + x;
    Radd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
    Rmul_1_l    : forall x, 1 * x == x;
    Rmul_comm    : forall x y, x * y == y * x;
    Rmul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
    Rdistr_l    : forall x y z, (x + y) * z == (x * z) + (y * z);
    Rsub_def    : forall x y, x - y == x + -y;
    Ropp_def    : forall x, x + (- x) == 0
 }.

 (** Equality is extensional *)

 Record sring_eq_ext : Prop := mk_seqe {
    (* SRing operators are compatible with equality *)
    SRadd_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 + y1 == x2 + y2;
    SRmul_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 * y1 == x2 * y2
  }.

 Record ring_eq_ext : Prop := mk_reqe {
    (* Ring operators are compatible with equality *)
    Radd_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 + y1 == x2 + y2;
    Rmul_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 * y1 == x2 * y2;
    Ropp_ext : forall x1 x2, x1 == x2 ->  -x1 == -x2
  }.

 (** Interpretation morphisms definition*)
 Section MORPHISM.
 Variable C:Type.
 Variable (cO cI : C) (cadd cmul csub : C->C->C) (copp : C->C).
 Variable ceqb : C->C->bool.
 (* [phi] est un morphisme de [C] dans [R] *)
 Variable phi : C -> R.
 Notation "x +! y" := (cadd x y). Notation "x -! y " := (csub x y).
 Notation "x *! y " := (cmul x y). Notation "-! x" := (copp x).
 Notation "x ?=! y" := (ceqb x y). Notation "[ x ]" := (phi x).

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
 Variable Rsth : Setoid_Theory R req.
   Add Setoid R req Rsth as R_setoid1.
 Variable reqb : R->R->bool.
 Hypothesis morph_req : forall x y, (reqb x y) = true -> x == y.
 Definition IDphi (x:R) := x.
 Lemma IDmorph : ring_morph rO rI radd rmul rsub ropp reqb IDphi.
 Proof.
  apply (mkmorph rO rI radd rmul rsub ropp reqb IDphi);intros;unfold IDphi;
  try apply (Seq_refl _ _ Rsth);auto.
 Qed.

 (** Specification of the power function *)
 Section POWER.
  Variable Cpow : Set.
  Variable Cp_phi : N -> Cpow.
  Variable rpow : R -> Cpow -> R.

  Record power_theory : Prop := mkpow_th {
    rpow_pow_N : forall r n, req (rpow r (Cp_phi n)) (pow_N rI rmul r n)
  }.

 End POWER.

 Definition pow_N_th := mkpow_th id_phi_N (pow_N rI rmul) (pow_N_pow_N rI rmul Rsth).


End DEFINITIONS.



Section ALMOST_RING.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x == y" := (req x y).

 (** Leibniz equality leads to a setoid theory and is extensional*)
 Lemma Eqsth : Setoid_Theory R (@eq R).
 Proof.  constructor;red;intros;subst;trivial. Qed.

 Lemma Eq_s_ext : sring_eq_ext radd rmul (@eq R).
 Proof. constructor;intros;subst;trivial. Qed.

 Lemma Eq_ext : ring_eq_ext radd rmul ropp (@eq R).
 Proof. constructor;intros;subst;trivial. Qed.

 Variable Rsth : Setoid_Theory R req.
   Add Setoid R req Rsth as R_setoid2.
   Ltac sreflexivity := apply (Seq_refl _ _ Rsth).

 Section SEMI_RING.
 Variable SReqe : sring_eq_ext radd rmul req.
   Add Morphism radd : radd_ext1.  exact (SRadd_ext SReqe). Qed.
   Add Morphism rmul : rmul_ext1.  exact (SRmul_ext SReqe). Qed.
 Variable SRth : semi_ring_theory 0 1 radd rmul req.

 (** Every semi ring can be seen as an almost ring, by taking :
        -x = x and x - y = x + y *)
 Definition SRopp (x:R) := x. Notation "- x" := (SRopp x).

 Definition SRsub x y := x + -y. Notation "x - y " := (SRsub x y).

 Lemma SRopp_ext : forall x y, x == y -> -x == -y.
 Proof. intros x y H;exact H. Qed.

 Lemma SReqe_Reqe : ring_eq_ext radd rmul SRopp req.
 Proof.
  constructor.  exact (SRadd_ext SReqe). exact (SRmul_ext SReqe).
  exact SRopp_ext.
 Qed.

 Lemma SRopp_mul_l : forall x y, -(x * y) == -x * y.
 Proof. intros;sreflexivity. Qed.

 Lemma SRopp_add : forall x y, -(x + y) == -x + -y.
 Proof. intros;sreflexivity.  Qed.


 Lemma SRsub_def   : forall x y, x - y == x + -y.
 Proof. intros;sreflexivity. Qed.

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
  apply mkmorph;intros;try sreflexivity.  unfold IDphi;auto.
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
 case Smorph; intros; constructor; auto.
 unfold SRopp in |- *; intros.
  setoid_reflexivity.
 Qed.

 End  SEMI_RING.

 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd : radd_ext2.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext2.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext2.  exact (Ropp_ext Reqe). Qed.

 Section RING.
 Variable Rth : ring_theory 0 1 radd rmul rsub ropp req.

 (** Rings are almost rings*)
 Lemma Rmul_0_l : forall x, 0 * x == 0.
 Proof.
  intro x; setoid_replace (0*x) with ((0+1)*x + -x).
  rewrite (Radd_0_l Rth); rewrite (Rmul_1_l Rth).
  rewrite (Ropp_def Rth);sreflexivity.

  rewrite (Rdistr_l Rth);rewrite (Rmul_1_l Rth).
  rewrite <- (Radd_assoc Rth); rewrite (Ropp_def Rth).
  rewrite (Radd_comm Rth); rewrite (Radd_0_l Rth);sreflexivity.
 Qed.

 Lemma Ropp_mul_l : forall x y, -(x * y) == -x * y.
 Proof.
  intros x y;rewrite <-(Radd_0_l Rth (- x * y)).
  rewrite (Radd_comm Rth).
  rewrite <-(Ropp_def Rth (x*y)).
  rewrite (Radd_assoc Rth).
  rewrite <- (Rdistr_l Rth).
  rewrite (Rth.(Radd_comm) (-x));rewrite (Ropp_def Rth).
  rewrite Rmul_0_l;rewrite (Radd_0_l Rth);sreflexivity.
 Qed.

 Lemma Ropp_add : forall x y, -(x + y) == -x + -y.
 Proof.
  intros x y;rewrite <- ((Radd_0_l Rth) (-(x+y))).
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
  rewrite ((Radd_comm Rth) y);rewrite (Ropp_def Rth).
  rewrite ((Radd_comm Rth) (-x) 0);rewrite (Radd_0_l Rth).
  apply (Radd_comm Rth).
 Qed.

 Lemma Ropp_opp : forall x, - -x == x.
 Proof.
  intros x; rewrite <- (Radd_0_l Rth (- -x)).
  rewrite <- (Ropp_def Rth x).
  rewrite <- (Radd_assoc Rth); rewrite (Ropp_def Rth).
  rewrite ((Radd_comm Rth) x);apply (Radd_0_l Rth).
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
  Notation "x +! y" := (cadd x y).  Notation "x *! y " := (cmul x y).
  Notation "x -! y " := (csub x y).  Notation "-! x" := (copp x).
  Notation "x ?=! y" := (ceqb x y). Notation "[ x ]" := (phi x).
 Variable Csth : Setoid_Theory C ceq.
 Variable Ceqe : ring_eq_ext cadd cmul copp ceq.
   Add Setoid C ceq Csth as C_setoid.
   Add Morphism cadd : cadd_ext.  exact (Radd_ext Ceqe). Qed.
   Add Morphism cmul : cmul_ext.  exact (Rmul_ext Ceqe). Qed.
   Add Morphism copp : copp_ext.  exact (Ropp_ext Ceqe). Qed.
 Variable Cth : ring_theory cO cI cadd cmul csub copp ceq.
 Variable Smorph : semi_morph 0 1 radd rmul req cO cI cadd cmul ceqb phi.
 Variable phi_ext : forall x y, ceq x y -> [x] == [y].
   Add Morphism phi : phi_ext1.  exact phi_ext. Qed.
 Lemma Smorph_opp : forall x, [-!x] == -[x].
 Proof.
  intros x;rewrite <-  (Rth.(Radd_0_l) [-!x]).
  rewrite <- ((Ropp_def Rth) [x]).
  rewrite ((Radd_comm Rth) [x]).
  rewrite <- (Radd_assoc Rth).
  rewrite <- (Smorph_add Smorph).
  rewrite (Ropp_def Cth).
  rewrite (Smorph0 Smorph).
  rewrite (Radd_comm Rth (-[x])).
  apply (Radd_0_l Rth);sreflexivity.
 Qed.

 Lemma Smorph_sub : forall x y, [x -! y] == [x] - [y].
 Proof.
  intros x y; rewrite (Rsub_def Cth);rewrite (Rsub_def Rth).
  rewrite (Smorph_add Smorph);rewrite Smorph_opp;sreflexivity.
 Qed.

 Lemma Smorph_morph : ring_morph 0 1 radd rmul rsub ropp req
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

 Lemma ARsub_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 - y1 == x2 - y2.
 Proof.
  intros.
  setoid_replace (x1 - y1) with (x1 + -y1).
  setoid_replace (x2 - y2) with (x2 + -y2).
  rewrite H;rewrite H0;sreflexivity.
  apply (ARsub_def ARth).
  apply (ARsub_def ARth).
 Qed.
   Add Morphism rsub : rsub_ext.  exact ARsub_ext. Qed.

 Ltac mrewrite :=
   repeat first
     [ rewrite (ARadd_0_l ARth)
     | rewrite <- ((ARadd_comm ARth) 0)
     | rewrite (ARmul_1_l ARth)
     | rewrite <- ((ARmul_comm ARth) 1)
     | rewrite (ARmul_0_l ARth)
     | rewrite <- ((ARmul_comm ARth) 0)
     | rewrite (ARdistr_l ARth)
     | sreflexivity
     | match goal with
       | |- context [?z * (?x + ?y)] => rewrite ((ARmul_comm ARth) z (x+y))
       end].

 Lemma ARadd_0_r : forall x, (x + 0) == x.
 Proof. intros; mrewrite. Qed.

 Lemma ARmul_1_r   : forall x, x * 1 == x.
 Proof. intros;mrewrite. Qed.

 Lemma ARmul_0_r : forall x, x * 0 == 0.
 Proof. intros;mrewrite. Qed.

 Lemma ARdistr_r : forall x y z, z * (x + y) == z*x + z*y.
 Proof.
  intros;mrewrite.
  repeat rewrite (ARth.(ARmul_comm) z);sreflexivity.
 Qed.

 Lemma ARadd_assoc1 : forall x y z, (x + y) + z == (y + z) + x.
 Proof.
  intros;rewrite <-(ARth.(ARadd_assoc) x).
  rewrite (ARth.(ARadd_comm) x);sreflexivity.
 Qed.

 Lemma ARadd_assoc2 : forall x y z, (y + x) + z == (y + z) + x.
 Proof.
  intros; repeat rewrite <- (ARadd_assoc ARth);
   rewrite ((ARadd_comm ARth) x); sreflexivity.
 Qed.

 Lemma ARmul_assoc1 : forall x y z, (x * y) * z == (y * z) * x.
 Proof.
  intros;rewrite <-((ARmul_assoc ARth) x).
  rewrite ((ARmul_comm ARth) x);sreflexivity.
 Qed.

 Lemma ARmul_assoc2 : forall x y z, (y * x) * z == (y * z) * x.
 Proof.
  intros; repeat rewrite <- (ARmul_assoc ARth);
   rewrite ((ARmul_comm ARth) x); sreflexivity.
 Qed.

 Lemma ARopp_mul_r : forall x y,  - (x * y) == x * -y.
 Proof.
  intros;rewrite ((ARmul_comm ARth) x y);
   rewrite (ARopp_mul_l ARth); apply (ARmul_comm ARth).
 Qed.

 Lemma ARopp_zero : -0 == 0.
 Proof.
  rewrite <- (ARmul_0_r 0); rewrite (ARopp_mul_l ARth).
  repeat rewrite ARmul_0_r; sreflexivity.
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

Ltac gen_add_push add Rsth Reqe ARth x :=
  repeat (match goal with
  | |- context [add (add ?y x) ?z] =>
     progress rewrite (ARadd_assoc2 Rsth Reqe ARth x y z)
  | |- context [add (add x ?y) ?z] =>
     progress rewrite (ARadd_assoc1 Rsth ARth x y z)
  end).

Ltac gen_mul_push mul Rsth Reqe ARth x :=
  repeat (match goal with
  | |- context [mul (mul ?y x) ?z] =>
     progress rewrite (ARmul_assoc2 Rsth Reqe ARth x y z)
  | |- context [mul (mul x ?y) ?z] =>
     progress rewrite (ARmul_assoc1 Rsth ARth x y z)
  end).

