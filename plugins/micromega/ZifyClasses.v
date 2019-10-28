(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Set Primitive Projections.

(** An alternative to [zify] in ML parametrised by user-provided classes instances.

    The framework has currently several limitations that are in place for simplicity.
    For instance, we only consider binary operators of type [Op: S -> S -> S].
    Another limitation is that our injection theorems e.g. [TBOpInj],
    are using Leibniz equality; the payoff is that there is no need for morphisms...
 *)

(** An injection [InjTyp S T] declares an injection
    from source type S to target type T.
*)
Class InjTyp (S : Type) (T : Type) :=
  mkinj {
      (* [inj] is the injection function *)
      inj  : S -> T;
      pred : T -> Prop;
      (* [cstr] states that [pred] holds for any injected element.
         [cstr (inj x)] is introduced in the goal for any leaf
         term of the form [inj x]
       *)
      cstr : forall x, pred (inj x)
    }.

(** [BinOp Op] declares a source operator [Op: S1 -> S2 -> S3].
 *)
Class BinOp {S1 S2 S3:Type} {T:Type} (Op : S1 -> S2 -> S3) {I1 : InjTyp S1 T} {I2 : InjTyp S2 T} {I3 : InjTyp S3 T} :=
  mkbop {
      (* [TBOp] is the target operator after injection of operands. *)
      TBOp : T -> T -> T;
      (* [TBOpInj] states the correctness of the injection. *)
      TBOpInj : forall (n:S1) (m:S2), inj (Op n m) = TBOp (inj n) (inj m)
    }.

(** [Unop Op] declares a source operator [Op : S1 -> S2]. *)
Class UnOp {S1 S2 T:Type} (Op : S1 -> S2) {I1 : InjTyp S1 T} {I2 : InjTyp S2 T}  :=
  mkuop {
      (* [TUOp] is the target operator after injection of operands. *)
      TUOp : T -> T;
      (* [TUOpInj] states the correctness of the injection. *)
      TUOpInj : forall (x:S1), inj (Op x) = TUOp (inj x)
    }.

(** [CstOp Op] declares a source constant [Op : S]. *)
Class CstOp {S T:Type} (Op : S) {I : InjTyp S T} :=
  mkcst {
      (* [TCst] is the target constant. *)
      TCst : T;
      (* [TCstInj] states the correctness of the injection. *)
      TCstInj : inj Op = TCst
    }.

(** In the framework, [Prop] is mapped to [Prop] and the injection is phrased in
    terms  of [=] instead of [<->].
*)

(** [BinRel R] declares the injection of a binary relation. *)
Class BinRel {S:Type} {T:Type} (R : S -> S -> Prop) {I : InjTyp S T}  :=
    mkbrel {
        TR : T -> T -> Prop;
        TRInj : forall n m : S, R n m <->  TR (@inj _ _ I n) (inj m)
      }.

(** [PropOp Op] declares morphisms for [<->].
    This will be used to deal with e.g. [and], [or],... *)
Class PropOp (Op : Prop -> Prop -> Prop) :=
  mkprop {
      op_iff : forall (p1 p2 q1 q2:Prop), (p1 <-> q1) -> (p2 <-> q2) -> (Op p1 p2 <-> Op q1 q2)
    }.

Class PropUOp (Op : Prop -> Prop) :=
  mkuprop {
      uop_iff : forall (p1 q1 :Prop), (p1 <-> q1) -> (Op p1 <-> Op q1)
    }.



(** Once the term is injected, terms can be replaced by their specification.
    NB: This is not sufficient to cope with [Z.div] or [Z.mod]
 *)
Class BinOpSpec {S T: Type} (Op : T -> T -> T) {I : InjTyp S T} :=
  mkbspec {
      BPred : T -> T -> T -> Prop;
      BSpec : forall x y, BPred x y (Op x y)
    }.

Class UnOpSpec {S T: Type} (Op : T -> T) {I : InjTyp S T} :=
  mkuspec {
      UPred : T -> T -> Prop;
      USpec : forall x, UPred x (Op x)
    }.

(** After injections, e.g. nat -> Z,
    the fact that Z.of_nat x * Z.of_nat y is positive is lost.
    This information can be recovered using instance of the  [Saturate] class.
*)
Class Saturate {T: Type} (Op : T -> T -> T) :=
  mksat {
      (** Given [Op x y],
          - [PArg1] is the pre-condition of x
          - [PArg2] is the pre-condition of y
          - [PRes]  is the pos-condition of (Op x y) *)
      PArg1 : T -> Prop;
      PArg2 : T -> Prop;
      PRes  : T -> Prop;
      (** [SatOk] states the correctness of the reasoning *)
      SatOk : forall x y, PArg1 x -> PArg2 y -> PRes (Op x y)
    }.
(* The [ZifyInst.saturate] iterates over all the instances
   and for every pattern of the form
   [H1 : PArg1 ?x , H2 : PArg2 ?y , T : context[Op ?x ?y] |- _ ]
   [H1 : PArg1 ?x , H2 : PArg2 ?y |- context[Op ?x ?y] ]
   asserts  (SatOK x y H1 H2) *)

(** The rest of the file is for internal use by the ML tactic.
    There are  data-structures and lemmas used to inductively construct
    the injected terms. *)

(** The data-structures [injterm] and [injected_prop]
    are used to store source and target expressions together
    with a correctness proof. *)

Record injterm {S T: Type} {I : S -> T} :=
  mkinjterm { source : S ; target : T ; inj_ok : I source = target}.

Record injprop  :=
  mkinjprop {
      source_prop : Prop ; target_prop : Prop ;
      injprop_ok : source_prop <-> target_prop}.

(** Lemmas for building [injterm] and [injprop]. *)

Definition mkprop_op  (Op : Prop -> Prop -> Prop) (POp : PropOp Op)
           (p1 :injprop) (p2: injprop) : injprop :=
  {| source_prop := (Op (source_prop p1) (source_prop p2)) ;
     target_prop := (Op (target_prop p1) (target_prop p2)) ;
     injprop_ok  := (op_iff (source_prop p1) (source_prop p2) (target_prop p1) (target_prop p2)
                            (injprop_ok p1) (injprop_ok p2))
  |}.


Definition mkuprop_op  (Op : Prop -> Prop) (POp : PropUOp Op)
           (p1 :injprop)  : injprop :=
  {| source_prop := (Op (source_prop p1)) ;
     target_prop := (Op (target_prop p1)) ;
     injprop_ok  := (uop_iff (source_prop p1) (target_prop p1)  (injprop_ok p1))
  |}.


Lemma mkapp2 (S1 S2 S3 T : Type) (Op : S1 -> S2 -> S3)
      {I1 : InjTyp S1 T} {I2 : InjTyp S2 T} {I3 : InjTyp S3 T}
         (B : @BinOp S1 S2 S3 T Op I1 I2 I3)
         (t1 : @injterm S1 T inj) (t2 : @injterm S2 T inj)
         : @injterm S3 T inj.
Proof.
  apply (mkinjterm _ _ inj (Op (source t1) (source t2)) (TBOp (target t1) (target t2))).
   (rewrite <- inj_ok;
    rewrite <- inj_ok;
    apply TBOpInj).
Defined.

Lemma mkapp (S1 S2 T : Type) (Op : S1 -> S2)
      {I1 : InjTyp S1 T}
      {I2 : InjTyp S2 T}
      (B : @UnOp S1 S2 T Op I1 I2 )
      (t1 : @injterm S1 T inj)
         : @injterm S2 T inj.
Proof.
  apply (mkinjterm _ _ inj (Op (source t1)) (TUOp (target t1))).
  (rewrite <- inj_ok; apply TUOpInj).
Defined.

Lemma mkapp0 (S T : Type) (Op : S)
      {I : InjTyp S T}
      (B : @CstOp S T Op I)
         : @injterm S T inj.
Proof.
  apply (mkinjterm _ _ inj Op  TCst).
   (apply TCstInj).
Defined.

Lemma mkrel (S T : Type) (R : S -> S -> Prop)
         {Inj : InjTyp S T}
         (B : @BinRel S T R Inj)
         (t1 : @injterm S T inj) (t2 : @injterm S T inj)
         : @injprop.
Proof.
  apply (mkinjprop  (R (source t1) (source t2)) (TR (target t1) (target t2))).
  (rewrite <- inj_ok; rewrite <- inj_ok;apply TRInj).
Defined.

(** Registering constants for use by the plugin *)
Register target_prop as ZifyClasses.target_prop.
Register mkrel       as ZifyClasses.mkrel.
Register target      as ZifyClasses.target.
Register mkapp2      as ZifyClasses.mkapp2.
Register mkapp       as ZifyClasses.mkapp.
Register mkapp0      as ZifyClasses.mkapp0.
Register op_iff      as ZifyClasses.op_iff.
Register uop_iff     as ZifyClasses.uop_iff.
Register TR          as ZifyClasses.TR.
Register TBOp        as ZifyClasses.TBOp.
Register TUOp        as ZifyClasses.TUOp.
Register TCst        as ZifyClasses.TCst.
Register mkprop_op   as ZifyClasses.mkprop_op.
Register mkuprop_op  as ZifyClasses.mkuprop_op.
Register injprop_ok  as ZifyClasses.injprop_ok.
Register inj_ok      as ZifyClasses.inj_ok.
Register source      as ZifyClasses.source.
Register source_prop as ZifyClasses.source_prop.
Register inj         as ZifyClasses.inj.
Register TRInj       as ZifyClasses.TRInj.
Register TUOpInj     as ZifyClasses.TUOpInj.
Register not         as ZifyClasses.not.
Register mkinjterm   as ZifyClasses.mkinjterm.
Register eq_refl     as ZifyClasses.eq_refl.
Register mkinjprop   as ZifyClasses.mkinjprop.
Register iff_refl    as ZifyClasses.iff_refl.
Register source_prop as ZifyClasses.source_prop.
Register injprop_ok  as ZifyClasses.injprop_ok.
Register iff         as ZifyClasses.iff.
