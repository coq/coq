Require Import TestSuite.admit.
Require Coq.Setoids.Setoid.

Axiom BITS : nat -> Set.
Definition n7 := 7.
Definition n15 := 15.
Definition n31 := 31.
Notation n8 := (S n7).
Notation n16 := (S n15).
Notation n32 := (S n31).
Inductive OpSize := OpSize1 | OpSize2 | OpSize4  .
Definition VWORD s := BITS (match s with OpSize1 => n8 | OpSize2 => n16 | OpSize4 => n32   end).
Definition BYTE   := VWORD OpSize1.
Definition WORD   := VWORD OpSize2.
Definition DWORD  := VWORD OpSize4.
Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.
Import Coq.Setoids.Setoid.
Class Equiv (A : Type) := equiv : relation A.
Infix "===" := equiv (at level 70, no associativity).
Class type (A : Type) {e : Equiv A} := eq_equiv : Equivalence equiv.
Definition setoid_resp {T T'} (f : T -> T') `{e : type T} `{e' : type T'} := forall x y, x === y -> f x === f y.
Record morphism T T' `{e : type T} `{e' : type T'} :=
  mkMorph {
      morph :> T -> T';
      morph_resp : setoid_resp morph}.
Arguments mkMorph [T T' e0 e e1 e'].
Infix "-s>" := morphism (at level 45, right associativity).
Section Morphisms.
  Context {S T U V} `{eS : type S} `{eT : type T} `{eU : type U} `{eV : type V}.
  Global Instance morph_equiv : Equiv (S -s> T).
  admit.
  Defined.

  Global Instance morph_type : type (S -s> T).
  admit.
  Defined.

  Program Definition mcomp (f: T -s> U) (g: S -s> T) : (S -s> U) :=
    mkMorph (fun x => f (g x)) _.
  Next Obligation.
    admit.
  Defined.

End Morphisms.

Infix "<<" := mcomp (at level 35).

Section MorphConsts.
  Context {S T U V} `{eS : type S} `{eT : type T} `{eU : type U} `{eV : type V}.

  Definition lift2s (f : S -> T -> U) p q : (S -s> T -s> U) :=
    mkMorph (fun x => mkMorph (f x) (p x)) q.

End MorphConsts.
Instance Equiv_PropP : Equiv Prop.
admit.
Defined.

Section SetoidProducts.
  Context {A B : Type} `{eA : type A} `{eB : type B}.
  Global Instance Equiv_prod : Equiv (A * B).
  admit.
  Defined.

  Global Instance type_prod : type (A * B).
  admit.
  Defined.

  Program Definition mfst : (A * B) -s> A :=
    mkMorph (fun p => fst p) _.
  Next Obligation.
    admit.
  Defined.

  Program Definition msnd : (A * B) -s> B :=
    mkMorph (fun p => snd p) _.
  Next Obligation.
    admit.
  Defined.

  Context {C} `{eC : type C}.

  Program Definition mprod (f: C -s> A) (g: C -s> B) : C -s> (A * B) :=
    mkMorph (fun c => (f c, g c)) _.
  Next Obligation.
    admit.
  Defined.

End SetoidProducts.

Section IndexedProducts.

  Record ttyp := {carr :> Type; eqc : Equiv carr; eqok : type carr}.
  Global Instance ttyp_proj_eq {A : ttyp} : Equiv A.
  admit.
  Defined.
  Global Instance ttyp_proj_prop {A : ttyp} : type A.
  admit.
  Defined.
  Context {I : Type} {P : I -> ttyp}.

  Global Program Instance Equiv_prodI : Equiv (forall i, P i) :=
    fun p p' : forall i, P i => (forall i : I, @equiv _ (eqc _) (p i) (p' i)).

  Global Instance type_prodI : type (forall i, P i).
  admit.
  Defined.

  Program Definition mprojI (i : I) : (forall i, P i) -s> P i :=
    mkMorph (fun X => X i) _.
  Next Obligation.
    admit.
  Defined.

  Context {C : Type} `{eC : type C}.

  Program Definition mprodI (f : forall i, C -s> P i) : C -s> (forall i, P i) :=
    mkMorph (fun c i => f i c) _.
  Next Obligation.
    admit.
  Defined.

End IndexedProducts.

Section Exponentials.

  Context {A B C D} `{eA : type A} `{eB : type B} `{eC : type C} `{eD : type D}.

  Program Definition comps : (B -s> C) -s> (A -s> B) -s> A -s> C :=
    lift2s (fun f g => f << g) _ _.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.

  Program Definition muncurry (f : A -s> B -s> C) : A * B -s> C :=
    mkMorph (fun p => f (fst p) (snd p)) _.
  Next Obligation.
    admit.
  Defined.

  Program Definition mcurry (f : A * B -s> C) : A -s> B -s> C :=
    lift2s (fun a b => f (a, b)) _ _.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.

  Program Definition meval : (B -s> A) * B -s> A :=
    mkMorph (fun p => fst p (snd p)) _.
  Next Obligation.
    admit.
  Defined.

  Program Definition mid : A -s> A := mkMorph (fun x => x) _.
  Next Obligation.
    admit.
  Defined.

  Program Definition mconst (b : B) : A -s> B := mkMorph (fun _ => b) _.
  Next Obligation.
    admit.
  Defined.

End Exponentials.

Inductive empty : Set := .
Instance empty_Equiv : Equiv empty.
admit.
Defined.
Instance empty_type : type empty.
admit.
Defined.

Section Initials.
  Context {A} `{eA : type A}.

  Program Definition mzero_init : empty -s> A := mkMorph (fun x => match x with end) _.
  Next Obligation.
    admit.
  Defined.

End Initials.

Section Subsetoid.

  Context {A} `{eA : type A} {P : A -> Prop}.
  Global Instance subset_Equiv : Equiv {a : A | P a}.
  admit.
  Defined.
  Global Instance subset_type : type {a : A | P a}.
  admit.
  Defined.

  Program Definition mforget : {a : A | P a} -s> A :=
    mkMorph (fun x => x) _.
  Next Obligation.
    admit.
  Defined.

  Context {B} `{eB : type B}.
  Program Definition minherit (f : B -s> A) (HB : forall b, P (f b)) : B -s> {a : A | P a} :=
    mkMorph (fun b => exist P (f b) (HB b)) _.
  Next Obligation.
    admit.
  Defined.

End Subsetoid.

Section Option.

  Context {A} `{eA : type A}.
  Global Instance option_Equiv : Equiv (option A).
  admit.
  Defined.

  Global Instance option_type : type (option A).
  admit.
  Defined.

End Option.

Section OptDefs.
  Context {A B} `{eA : type A} `{eB : type B}.

  Program Definition msome : A -s> option A := mkMorph (fun a => Some a) _.
  Next Obligation.
    admit.
  Defined.

  Program Definition moptionbind (f : A -s> option B) : option A -s> option B :=
    mkMorph (fun oa => match oa with None => None | Some a => f a end) _.
  Next Obligation.
    admit.
  Defined.

End OptDefs.

Generalizable Variables Frm.

Class ILogicOps Frm := {
                        lentails: relation Frm;
                        ltrue: Frm;
                        lfalse: Frm;
                        limpl: Frm -> Frm -> Frm;
                        land: Frm -> Frm -> Frm;
                        lor: Frm -> Frm -> Frm;
                        lforall: forall {T}, (T -> Frm) -> Frm;
                        lexists: forall {T}, (T -> Frm) -> Frm
                      }.

Infix "|--"  := lentails (at level 79, no associativity).
Infix "//\\"   := land (at level 75, right associativity).
Infix "\\//"   := lor (at level 76, right associativity).
Infix "-->>"   := limpl (at level 77, right associativity).
Notation "'Forall' x .. y , p" :=
  (lforall (fun x => .. (lforall (fun y => p)) .. )) (at level 78, x binder, y binder, right associativity).
Notation "'Exists' x .. y , p" :=
  (lexists (fun x => .. (lexists (fun y => p)) .. )) (at level 78, x binder, y binder, right associativity).

Class ILogic Frm {ILOps: ILogicOps Frm} := {
                                            lentailsPre:> PreOrder lentails;
                                            ltrueR: forall C, C |-- ltrue;
                                            lfalseL: forall C, lfalse |-- C;
                                            lforallL: forall T x (P: T -> Frm) C, P x |-- C -> lforall P |-- C;
                                            lforallR: forall T (P: T -> Frm) C, (forall x, C |-- P x) -> C |-- lforall P;
                                            lexistsL: forall T (P: T -> Frm) C, (forall x, P x |-- C) -> lexists P |-- C;
                                            lexistsR: forall T x (P: T -> Frm) C, C |-- P x -> C |-- lexists P;
                                            landL1: forall P Q C, P |-- C  ->  P //\\ Q |-- C;
                                            landL2: forall P Q C, Q |-- C  ->  P //\\ Q |-- C;
                                            lorR1:  forall P Q C, C |-- P  ->  C |-- P \\// Q;
                                            lorR2:  forall P Q C, C |-- Q  ->  C |-- P \\// Q;
                                            landR:  forall P Q C, C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q;
                                            lorL:   forall P Q C, P |-- C  ->  Q |-- C  ->  P \\// Q |-- C;
                                            landAdj: forall P Q C, C |-- (P -->> Q) -> C //\\ P |-- Q;
                                            limplAdj: forall P Q C, C //\\ P |-- Q -> C |-- (P -->> Q)
                                          }.
Hint Extern 0 (?x |-- ?x) => reflexivity.

Section ILogicExtra.
  Context `{IL: ILogic Frm}.
  Definition lpropand (p: Prop) Q := Exists _: p, Q.
  Definition lpropimpl (p: Prop) Q := Forall _: p, Q.

End ILogicExtra.

Infix "/\\" := lpropand (at level 75, right associativity).
Infix "->>" := lpropimpl (at level 77, right associativity).

Section ILogic_Fun.
  Context (T: Type) `{TType: type T}.
  Context `{IL: ILogic Frm}.

  Record ILFunFrm := mkILFunFrm {
                         ILFunFrm_pred :> T -> Frm;
                         ILFunFrm_closed: forall t t': T, t === t' ->
                                                          ILFunFrm_pred t |-- ILFunFrm_pred t'
                       }.

  Notation "'mk'" := @mkILFunFrm.

  Program Definition ILFun_Ops : ILogicOps ILFunFrm := {|
                                                        lentails P Q := forall t:T, P t |-- Q t;
                                                        ltrue        := mk (fun t => ltrue) _;
                                                        lfalse       := mk (fun t => lfalse) _;
                                                        limpl    P Q := mk (fun t => P t -->> Q t) _;
                                                        land     P Q := mk (fun t => P t //\\ Q t) _;
                                                        lor      P Q := mk (fun t => P t \\// Q t) _;
                                                        lforall  A P := mk (fun t => Forall a, P a t) _;
                                                        lexists  A P := mk (fun t => Exists a, P a t) _
                                                      |}.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.

End ILogic_Fun.

Arguments ILFunFrm _ {e} _ {ILOps}.
Arguments mkILFunFrm [T] _ [Frm ILOps].

Program Definition ILFun_eq {T R} {ILOps: ILogicOps R} {ILogic: ILogic R} (P : T -> R) :
  @ILFunFrm T _ R ILOps :=
  @mkILFunFrm T eq R ILOps P _.
Next Obligation.
  admit.
Defined.

Instance ILogicOps_Prop : ILogicOps Prop | 2 := {|
                                                 lentails P Q := (P : Prop) -> Q;
                                                 ltrue        := True;
                                                 lfalse       := False;
                                                 limpl    P Q := P -> Q;
                                                 land     P Q := P /\ Q;
                                                 lor      P Q := P \/ Q;
                                                 lforall  T F := forall x:T, F x;
                                                 lexists  T F := exists x:T, F x
                                               |}.

Instance ILogic_Prop : ILogic Prop.
admit.
Defined.

Section FunEq.
  Context A `{eT: type A}.

  Global Instance FunEquiv {T} : Equiv (T -> A) := {
                                                    equiv P Q := forall a, P a === Q a
                                                  }.
End FunEq.

Section SepAlgSect.
  Class SepAlgOps T `{eT : type T}:= {
                                      sa_unit : T;

                                      sa_mul : T -> T -> T -> Prop
                                    }.

  Class SepAlg T `{SAOps: SepAlgOps T} : Type := {
                                                  sa_mul_eqL a b c d : sa_mul a b c -> c === d -> sa_mul a b d;
                                                  sa_mul_eqR a b c d : sa_mul a b c -> sa_mul a b d -> c === d;
                                                  sa_mon a b c   : a === b -> sa_mul a c === sa_mul b c;
                                                  sa_mulC a b        : sa_mul a b === sa_mul b a;
                                                  sa_mulA a b c      : forall bc abc, sa_mul a bc abc -> sa_mul b c bc ->
                                                                                      exists ac, sa_mul b ac abc /\ sa_mul a c ac;
                                                  sa_unitI a         : sa_mul a sa_unit a
                                                }.

End SepAlgSect.

Section BILogic.

  Class BILOperators (A : Type) := {
                                    empSP : A;
                                    sepSP : A -> A -> A;
                                    wandSP : A -> A -> A
                                  }.

End BILogic.

Notation "a '**' b"  := (sepSP a b)
                          (at level 75, right associativity).

Section BISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.

  Program Instance SABIOps: BILOperators (ILFunFrm A B) := {
                                                            empSP := mkILFunFrm e (fun x => sa_unit === x /\\ ltrue) _;
                                                            sepSP P Q := mkILFunFrm e (fun x => Exists x1, Exists x2, sa_mul x1 x2 x /\\
                                                                                                                             P x1 //\\ Q x2) _;
                                                            wandSP P Q := mkILFunFrm e (fun x => Forall x1, Forall x2, sa_mul x x1 x2 ->>
                                                                                                                              P x1 -->> Q x2) _
                                                          }.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.
  Next Obligation.
    admit.
  Defined.

End BISepAlg.

Set Implicit Arguments.

Definition Chan := WORD.
Definition Data := BYTE.

Inductive Action :=
| Out (c:Chan) (d:Data)
| In (c:Chan) (d:Data).

Definition Actions := list Action.

Instance ActionsEquiv : Equiv Actions := {
                                          equiv a1 a2 := a1 = a2
                                        }.

Definition OPred := ILFunFrm Actions Prop.
Definition mkOPred (P : Actions -> Prop) : OPred.
  admit.
Defined.

Definition eq_opred s := mkOPred (fun s' => s === s').
Definition empOP : OPred.
  exact (eq_opred nil).
Defined.
Definition catOP (P Q: OPred) : OPred.
  admit.
Defined.

Class IsPointed (T : Type) := point : T.

Generalizable All Variables.

Notation IsPointed_OPred P := (IsPointed (exists x : Actions, (P : OPred) x)).

Record PointedOPred := mkPointedOPred {
                           OPred_pred :> OPred;
                           OPred_inhabited: IsPointed_OPred OPred_pred
                         }.

Existing Instance OPred_inhabited.

Canonical Structure default_PointedOPred O `{IsPointed_OPred O} : PointedOPred
  := {| OPred_pred := O ; OPred_inhabited := _ |}.
Instance IsPointed_eq_opred x : IsPointed_OPred (eq_opred x).
admit.
Defined.
Instance IsPointed_catOP `{IsPointed_OPred P, IsPointed_OPred Q} : IsPointed_OPred (catOP P Q).
admit.
Defined.

Definition Flag  := BITS 5.
Definition OF: Flag.
  admit.
Defined.

Inductive FlagVal := mkFlag (b: bool) | FlagUnspecified.
Coercion mkFlag : bool >-> FlagVal.
Inductive NonSPReg := EAX | EBX | ECX | EDX | ESI | EDI | EBP.

Inductive Reg := nonSPReg (r: NonSPReg) | ESP.

Inductive AnyReg := regToAnyReg (r: Reg) | EIP.

Inductive BYTEReg := AL|BL|CL|DL|AH|BH|CH|DH.

Inductive WORDReg := mkWordReg (r:Reg).
Definition PState : Type.
admit.
Defined.

Instance PStateEquiv : Equiv PState.
admit.
Defined.

Instance PStateType : type PState.
admit.
Defined.

Instance PStateSepAlgOps: SepAlgOps PState.
admit.
Defined.
Definition SPred : Type.
exact (ILFunFrm PState Prop).
Defined.

Local Existing Instance ILFun_Ops.
Local Existing Instance SABIOps.
Axiom BYTEregIs : BYTEReg -> BYTE -> SPred.

Inductive RegOrFlag :=
| RegOrFlagDWORD :> AnyReg -> RegOrFlag
| RegOrFlagWORD :> WORDReg -> RegOrFlag
| RegOrFlagBYTE :> BYTEReg -> RegOrFlag
| RegOrFlagF :> Flag -> RegOrFlag.

Definition RegOrFlag_target rf :=
  match rf with
    | RegOrFlagDWORD _ => DWORD
    | RegOrFlagWORD _  => WORD
    | RegOrFlagBYTE _  => BYTE
    | RegOrFlagF _     => FlagVal
  end.

Inductive Condition :=
| CC_O | CC_B | CC_Z | CC_BE | CC_S | CC_P | CC_L | CC_LE.

Section ILSpecSect.

  Axiom spec : Type.
  Global Instance ILOps: ILogicOps spec | 2.
  admit.
  Defined.

End ILSpecSect.

Axiom parameterized_basic : forall {T_OPred} {proj : T_OPred -> OPred} {T} (P : SPred) (c : T) (O : OPred) (Q : SPred), spec.
Global Notation loopy_basic := (@parameterized_basic PointedOPred OPred_pred _).

Axiom program : Type.

Axiom ConditionIs : forall (cc : Condition) (cv : RegOrFlag_target OF), SPred.

Axiom foldl : forall {T R}, (R -> T -> R) -> R -> list T -> R.
Axiom nth : forall {T}, T -> list T -> nat -> T.
Axiom while : forall (ptest: program)
                     (cond: Condition) (value: bool)
                     (pbody: program), program.

Lemma while_rule_ind {quantT}
      {ptest} {cond : Condition} {value : bool} {pbody}
      {S}
      {transition_body : quantT -> quantT}
      {P : quantT -> SPred} {Otest : quantT -> OPred} {Obody : quantT -> OPred} {O : quantT -> PointedOPred}
      {O_after_test : quantT -> PointedOPred}
      {I_state : quantT -> bool -> SPred}
      {I_logic : quantT -> bool -> bool}
      {Q : quantT -> SPred}
      (Htest : S |-- (Forall (x : quantT),
                      (loopy_basic (P x)
                                   ptest
                                   (Otest x)
                                   (Exists b, I_logic x b = true /\\ I_state x b ** ConditionIs cond b))))
      (Hbody : S |-- (Forall (x : quantT),
                      (loopy_basic (I_logic x value = true /\\ I_state x value ** ConditionIs cond value)
                                   pbody
                                   (Obody x)
                                   (P (transition_body x)))))
      (H_after_test : forall x, catOP (Otest x) (O_after_test x) |-- O x)
      (H_body_after_test : forall x, I_logic x value = true -> catOP (Obody x) (O (transition_body x)) |-- O_after_test x)
      (H_empty : forall x, I_logic x (negb value) = true -> empOP |-- O_after_test x)
      (Q_correct : forall x, I_logic x (negb value) = true /\\ I_state x (negb value) ** ConditionIs cond (negb value) |-- Q x)
      (Q_safe : forall x, I_logic x value = true -> Q (transition_body x) |-- Q x)
: S |-- (Forall (x : quantT),
         loopy_basic (P x)
                     (while ptest cond value pbody)
                     (O x)
                     (Q x)).
admit.
Defined.
Axiom behead : forall {T}, list T -> list T.
Axiom all : forall {T}, (T -> bool) -> list T -> bool.
Axiom all_behead : forall {T} (xs : list T) P, all P xs = true -> all P (behead xs) = true.
Instance IsPointed_foldlOP A B C f g (init : A * B) `{IsPointed_OPred (g init)}
         `{forall a acc, IsPointed_OPred (g acc) -> IsPointed_OPred (g (f acc a))}
         (ls : list C)
: IsPointed_OPred (g (foldl f init ls)).
admit.
Defined.
Goal    forall (ptest : program) (cond : Condition) (value : bool)
               (pbody : program) (T ioT : Type) (P : T -> SPred)
               (I : T -> bool -> SPred) (accumulate : T -> ioT -> T)
               (Otest Obody : T -> ioT -> PointedOPred)
               (coq_test__is_finished : ioT -> bool) (S : spec)
               (al : BYTE),
          (forall (initial : T) (xs : list ioT) (x : ioT),
             all (fun t : ioT => negb (coq_test__is_finished t)) xs = true ->
             coq_test__is_finished x = true ->
             S
               |-- loopy_basic (P initial ** BYTEregIs AL al) ptest
               (Otest initial (nth x xs 0))
               (I initial
                  (match coq_test__is_finished (nth x xs 0) with true => negb value | false => value end) **
                  ConditionIs cond
                  (match coq_test__is_finished (nth x xs 0) with true => negb value | false => value end))) ->
          (forall (initial : T) (xs : list ioT) (x : ioT),
             all (fun t : ioT => negb (coq_test__is_finished t)) xs = true ->
             xs <> nil ->
             coq_test__is_finished x = true ->
             S
               |-- loopy_basic (I initial value ** ConditionIs cond value) pbody
               (Obody initial (nth x xs 0))
               (P (accumulate initial (nth x xs 0)) ** BYTEregIs AL al)) ->
          forall x : ioT,
            coq_test__is_finished x = true ->
            S
              |-- Forall ixsp : {init_xs : T * list ioT &
                                           all (fun t : ioT => negb (coq_test__is_finished t))
                                               (snd init_xs) = true},
  loopy_basic (P (fst (projT1 ixsp)) ** BYTEregIs AL al)
              (while ptest cond value pbody)
              (catOP
                 (snd
                    (foldl
                       (fun (xy : T * OPred) (v : ioT) =>
                          (accumulate (fst xy) v,
                           catOP (catOP (Otest (fst xy) v) (Obody (fst xy) v))
                                 (snd xy))) (fst (projT1 ixsp), empOP)
                       (snd (projT1 ixsp))))
                 (Otest (foldl accumulate (fst (projT1 ixsp)) (snd (projT1 ixsp)))
                        x))
              (I (foldl accumulate (fst (projT1 ixsp)) (snd (projT1 ixsp)))
                 (negb value) ** ConditionIs cond (negb value)).
  intros.
  eapply @while_rule_ind
  with (I_logic := fun ixsp b => match (match (coq_test__is_finished (nth x (snd (projT1 ixsp)) 0)) with true => negb value | false => value end), b with true, true => true | false, false => true | _, _ => false end)
         (Otest := fun ixsp => Otest (fst (projT1 ixsp)) (nth x (snd (projT1 ixsp)) 0))
         (Obody := fun ixsp => Obody (fst (projT1 ixsp)) (nth x (snd (projT1 ixsp)) 0))
         (I_state := fun ixsp => I (fst (projT1 ixsp)))
         (transition_body := fun ixsp => let initial := fst (projT1 ixsp) in
                                         let xs := snd (projT1 ixsp) in
                                         existT _ (accumulate initial (nth x xs 0), behead xs) _)
         (O_after_test := fun ixsp => let initial := fst (projT1 ixsp) in
                                      let xs := snd (projT1 ixsp) in
                                      match xs with | nil => default_PointedOPred empOP | _ => Obody initial (nth x xs 0) end);
    simpl projT1; simpl projT2; simpl fst; simpl snd; clear; let H := fresh in assert (H : False) by (clear; admit); destruct H.

  Grab Existential Variables.
  subst_body; simpl.
  Fail refine (all_behead (projT2 _)).
  Unset Solve Unification Constraints. refine (all_behead (projT2 _)).
