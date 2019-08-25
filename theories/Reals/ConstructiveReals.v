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
   All of its instances are isomorphic, for example it contains
   the Cauchy reals implemented in file ConstructivecauchyReals
   and the sumbool-based Dedekind reals defined by

Structure R := {
  (* The cuts are represented as propositional functions, rather than subsets,
     as there are no subsets in type theory. *)
  lower : Q -> Prop;
  upper : Q -> Prop;
  (* The cuts respect equality on Q. *)
  lower_proper : Proper (Qeq ==> iff) lower;
  upper_proper : Proper (Qeq ==> iff) upper;
  (* The cuts are inhabited. *)
  lower_bound : { q : Q | lower q };
  upper_bound : { r : Q | upper r };
  (* The lower cut is a lower set. *)
  lower_lower : forall q r, q < r -> lower r -> lower q;
  (* The lower cut is open. *)
  lower_open : forall q, lower q -> exists r, q < r /\ lower r;
  (* The upper cut is an upper set. *)
  upper_upper : forall q r, q < r -> upper q -> upper r;
  (* The upper cut is open. *)
  upper_open : forall r, upper r -> exists q,  q < r /\ upper q;
  (* The cuts are disjoint. *)
  disjoint : forall q, ~ (lower q /\ upper q);
  (* There is no gap between the cuts. *)
  located : forall q r, q < r -> { lower q } + { upper r }
}.

  see github.com/andrejbauer/dedekind-reals for the Prop-based
  version of those Dedekind reals (although Prop fails to make
  them an instance of ConstructiveReals). *)

Require Import QArith.

Definition isLinearOrder (X : Set) (Xlt : X -> X -> Set) : Set
  := (forall x y:X, Xlt x y -> Xlt y x -> False)
     * (forall x y z : X, Xlt x y -> Xlt y z -> Xlt x z)
     * (forall x y z : X, Xlt x z -> Xlt x y + Xlt y z).

Definition orderEq (X : Set) (Xlt : X -> X -> Set) (x y : X) : Prop
  := (Xlt x y -> False) /\ (Xlt y x -> False).

Definition orderAppart (X : Set) (Xlt : X -> X -> Set) (x y : X) : Set
  := Xlt x y  +  Xlt y x.

Definition sig_forall_dec_T : Type
  := forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Definition sig_not_dec_T : Type := forall P : Prop, { ~~P } + { ~P }.

Record ConstructiveReals : Type :=
  {
    CRcarrier : Set;
    CRlt : CRcarrier -> CRcarrier -> Set;
    CRltLinear : isLinearOrder CRcarrier CRlt;

    CRltProp : CRcarrier -> CRcarrier -> Prop;
    (* This choice algorithm can be slow, keep it for the classical
       quotient of the reals, where computations are blocked by
       axioms like LPO. *)
    CRltEpsilon : forall x y : CRcarrier, CRltProp x y -> CRlt x y;
    CRltForget : forall x y : CRcarrier, CRlt x y -> CRltProp x y;
    CRltDisjunctEpsilon : forall a b c d : CRcarrier,
        (CRltProp a b \/ CRltProp c d) -> CRlt a b  +  CRlt c d;

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
        CRlt r1 r2 -> CRlt (CRplus r r1) (CRplus r r2);
    CRplus_lt_reg_l : forall r r1 r2 : CRcarrier,
        CRlt (CRplus r r1) (CRplus r r2) -> CRlt r1 r2;
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
        { k : Z & CRlt x (gen_phiZ CRzero CRone CRplus CRmult CRopp k) };

    CRminus (x y : CRcarrier) : CRcarrier
    := CRplus x (CRopp y);
    CR_cv (un : nat -> CRcarrier) (l : CRcarrier) : Set
    := forall eps:CRcarrier,
        CRlt CRzero eps
        -> { p : nat & forall i:nat, le p i -> CRlt (CRopp eps) (CRminus (un i) l)
                                               * CRlt (CRminus (un i) l) eps };
    CR_cauchy (un : nat -> CRcarrier) : Set
    := forall eps:CRcarrier,
        CRlt CRzero eps
        -> { p : nat & forall i j:nat, le p i -> le p j ->
                                       CRlt (CRopp eps) (CRminus (un i) (un j))
                                       * CRlt (CRminus (un i) (un j)) eps };

    CR_complete :
      forall xn : nat -> CRcarrier, CR_cauchy xn -> { l : CRcarrier & CR_cv xn l };

    (* Those are redundant, they could be proved from the previous hypotheses *)
    CRis_upper_bound (E:CRcarrier -> Prop) (m:CRcarrier)
    := forall x:CRcarrier, E x -> CRlt m x -> False;

    CR_sig_lub :
      forall (E:CRcarrier -> Prop),
        sig_forall_dec_T
        -> sig_not_dec_T
        -> (exists x : CRcarrier, E x)
        -> (exists x : CRcarrier, CRis_upper_bound E x)
        -> { u : CRcarrier | CRis_upper_bound E u /\
                             forall y:CRcarrier, CRis_upper_bound E y -> CRlt y u -> False };
  }.
