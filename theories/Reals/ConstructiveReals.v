(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(* An interface for constructive and computable real numbers.
   All of its elements are isomorphic, for example it contains
   the Cauchy reals and the Dedekind reals. *)

Require Import QArith.

Definition isLinearOrder (X : Set) (Xlt : X -> X -> Prop) : Set
  := prod ((forall x y:X, Xlt x y -> ~Xlt y x)
           /\ (forall x y z : X, Xlt x y -> Xlt y z -> Xlt x z))
          (forall x y z : X, Xlt x z -> {Xlt x y} + {Xlt y z}).

Definition orderEq (X : Set) (Xlt : X -> X -> Prop) (x y : X) : Prop
  := ~Xlt x y /\ ~Xlt y x.

Definition orderAppart (X : Set) (Xlt : X -> X -> Prop) (x y : X) : Prop
  := Xlt x y \/ Xlt y x.

Definition sig_forall_dec_T : Type
  := forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Definition sig_not_dec_T : Type := forall P : Prop, { ~~P } + { ~P }.

Record ConstructiveReals : Type :=
  {
    CRcarrier : Set;
    CRlt : CRcarrier -> CRcarrier -> Prop;
    CRltLinear : isLinearOrder CRcarrier CRlt;

    (* Constants *)
    CRzero : CRcarrier;
    CRone : CRcarrier;

    (* Addition and multiplication *)
    CRplus : CRcarrier -> CRcarrier -> CRcarrier;
    CRopp : CRcarrier -> CRcarrier; (* Computable opposite,
                         stronger than Prop-existence of opposite *)
    CRmult : CRcarrier -> CRcarrier -> CRcarrier;

    CRisRing : ring_theory CRzero CRone CRplus CRmult
                          (fun x y => CRplus x (CRopp y)) CRopp (orderEq CRcarrier CRlt);
    CRisRingExt : ring_eq_ext CRplus CRmult CRopp (orderEq CRcarrier CRlt);

    (* Compatibility with order *)
    CRzero_lt_one : CRlt CRzero CRone; (* 0 # 1 would only allow 0 < 1 because
                                    of Fmult_lt_0_compat so request 0 < 1 directly. *)
    CRplus_lt_compat_l : forall r r1 r2 : CRcarrier,
        CRlt r1 r2 <-> CRlt (CRplus r r1) (CRplus r r2);
    CRmult_lt_0_compat : forall x y : CRcarrier,
        CRlt CRzero x -> CRlt CRzero y -> CRlt CRzero (CRmult x y);

    (* A constructive total inverse function on F would need to be continuous,
       which is impossible because we cannot connect plus and minus infinities.
       Therefore it has to be a partial function, defined on non zero elements.
       For this reason we cannot use Coq's field_theory and field tactic.

       To implement Finv by Cauchy sequences we need orderAppart,
       ~orderEq is not enough. *)
    CRinv : forall x : CRcarrier, orderAppart _ CRlt x CRzero -> CRcarrier;
    CRinv_l : forall (r:CRcarrier) (rnz : orderAppart _ CRlt r CRzero),
        orderEq _ CRlt (CRmult (CRinv r rnz) r) CRone;
    CRinv_0_lt_compat : forall (r : CRcarrier) (rnz : orderAppart _ CRlt r CRzero),
        CRlt CRzero r -> CRlt CRzero (CRinv r rnz);

    CRarchimedean : forall x : CRcarrier,
        { k : Z | CRlt x (gen_phiZ CRzero CRone CRplus CRmult CRopp k) };

    CRminus (x y : CRcarrier) : CRcarrier
    := CRplus x (CRopp y);
    CR_cv (un : nat -> CRcarrier) (l : CRcarrier) : Set
    := forall eps:CRcarrier,
        CRlt CRzero eps
        -> { p : nat | forall i:nat, le p i -> CRlt (CRopp eps) (CRminus (un i) l)
                                               /\ CRlt (CRminus (un i) l) eps };
    CR_cauchy (un : nat -> CRcarrier) : Set
    := forall eps:CRcarrier,
        CRlt CRzero eps
        -> { p : nat | forall i j:nat, le p i -> le p j ->
                                       CRlt (CRopp eps) (CRminus (un i) (un j))
                                       /\ CRlt (CRminus (un i) (un j)) eps };

    CR_complete :
      forall xn : nat -> CRcarrier, CR_cauchy xn -> { l : CRcarrier & CR_cv xn l };

    (* Those are redundant, they could be proved from the previous hypotheses *)
    CRlt_lpo_dec : forall x y : CRcarrier,
        sig_forall_dec_T
        -> { CRlt x y } + { ~CRlt x y };

    CRis_upper_bound (E:CRcarrier -> Prop) (m:CRcarrier)
    := forall x:CRcarrier, E x -> ~(CRlt m x);

    CR_sig_lub :
      forall (E:CRcarrier -> Prop),
        sig_forall_dec_T
        -> sig_not_dec_T
        -> (exists x : CRcarrier, E x)
        -> (exists x : CRcarrier, CRis_upper_bound E x)
        -> { u : CRcarrier | CRis_upper_bound E u /\
                             forall y:CRcarrier, CRis_upper_bound E y -> ~CRlt y u };

  }.
