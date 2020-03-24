(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-20019                            *)
(*                                                                      *)
(************************************************************************)

Require Import List.
Require Import Refl.
Require Import Bool.
Require Import Relation_Definitions Setoid.

Set Implicit Arguments.


Section S.
  Context {TA  : Type}. (* type of interpreted atoms *)
  Context {TX  : bool -> Type}. (* type of uninterpreted terms (Prop) *)
  Context {AA  : Type}. (* type of annotations for atoms *)
  Context {AF  : Type}. (* type of formulae identifiers *)

  Inductive GFormula  : forall (isProp:bool), Type :=
  | TT   : forall (b : bool), GFormula b
  | FF   : forall (b : bool), GFormula b
  | X    : forall (b : bool), TX b -> GFormula b
  | A    : forall (b : bool), TA -> AA -> GFormula b
  | AND  : forall (b : bool), GFormula b -> GFormula b -> GFormula b
  | OR   : forall (b : bool), GFormula b -> GFormula b -> GFormula b
  | NOT  : forall (b : bool), GFormula b -> GFormula b
  | IMPL : forall (b : bool), GFormula b -> option AF -> GFormula b -> GFormula b
  | IFF  : forall (b : bool), GFormula b -> GFormula b -> GFormula b
  | EQ   : GFormula false -> GFormula false -> GFormula true.

  Section MAPX.
    Variable F : forall b, TX b -> TX b.

    Fixpoint mapX (b:bool) (f : GFormula b) : GFormula b :=
      match f with
      | TT b => TT b
      | FF b => FF b
      | X x => X (F  x)
      | A b a an => A b a an
      | AND f1 f2 => AND (mapX f1) (mapX f2)
      | OR f1 f2  => OR (mapX f1) (mapX f2)
      | NOT f     => NOT (mapX f)
      | IMPL f1 o f2 => IMPL (mapX f1) o (mapX f2)
      | IFF f1 f2    => IFF (mapX f1) (mapX f2)
      | EQ f1 f2           => EQ (mapX f1) (mapX f2)
      end.

  End MAPX.

  Section FOLDANNOT.
    Variable ACC : Type.
    Variable F : ACC -> AA -> ACC.

    Fixpoint foldA (b: bool) (f : GFormula b) (acc : ACC) : ACC :=
      match f with
      | TT _ => acc
      | FF _ => acc
      | X x => acc
      | A _ a an => F acc an
      | AND f1 f2
      | OR f1 f2
      | IFF f1 f2
      | IMPL f1 _ f2 | EQ f1 f2 => foldA f1 (foldA f2 acc)
      | NOT f     => foldA f acc
      end.

  End FOLDANNOT.


  Definition cons_id (id : option AF) (l : list AF) :=
    match id with
    | None => l
    | Some id => id :: l
    end.

  Fixpoint ids_of_formula (b:bool) (f:GFormula b) :=
    match f with
    | IMPL f id f' => cons_id id (ids_of_formula f')
    |  _           => nil
    end.

  Fixpoint collect_annot (b:bool) (f : GFormula b) : list AA :=
    match f with
    | TT _ | FF _ | X _ => nil
    | A _ _ a => a ::nil
    | AND f1 f2
    | OR  f1 f2
    | IFF f1 f2 | EQ f1 f2
    | IMPL f1 _ f2  => collect_annot f1 ++ collect_annot f2
    | NOT  f  => collect_annot f
    end.

  Definition rtyp (b:bool) : Type := if b then Prop else bool.

  Variable ex : forall (b:bool), TX b -> rtyp b. (* [ex] will be the identity *)

  Section EVAL.

    Variable ea : forall (b:bool), TA -> rtyp b.

    Definition eTT (b:bool) : rtyp b :=
      if b as b' return  rtyp b' then True else true.

    Definition eFF (b:bool) : rtyp b :=
      if b as b' return  rtyp b' then False else false.

    Definition eAND (b :bool) : rtyp b -> rtyp b -> rtyp b :=
      if b as b' return rtyp b' -> rtyp b' -> rtyp b'
      then and else andb.

    Definition eOR (b :bool) : rtyp b -> rtyp b -> rtyp b :=
      if b as b' return rtyp b' -> rtyp b' -> rtyp b'
      then or else orb.

    Definition eIMPL (b :bool) : rtyp b -> rtyp b -> rtyp b :=
      if b as b' return rtyp b' -> rtyp b' -> rtyp b'
      then (fun x y => x -> y) else implb.

    Definition eIFF (b :bool) : rtyp b -> rtyp b -> rtyp b :=
      if b as b' return rtyp b' -> rtyp b' -> rtyp b'
      then iff else eqb.

    Definition eNOT (b :bool) : rtyp b -> rtyp b :=
      if b as b' return rtyp b' -> rtyp b'
      then not else negb.

    Fixpoint eval_f (b:bool) (f:GFormula b) {struct f}: rtyp b :=
      match f in GFormula b' return rtyp b' with
      | TT tb => eTT tb
      | FF tb => eFF tb
      | A b a _ =>  ea b a
      | X p => ex  p
      | @AND b e1 e2 => eAND b (eval_f  e1) (eval_f e2)
      | @OR b e1 e2  => eOR b (eval_f e1) (eval_f e2)
      | @NOT b e     => eNOT b (eval_f e)
      | @IMPL b f1 _ f2 => eIMPL b (eval_f f1)  (eval_f f2)
      | @IFF b f1 f2    => eIFF b (eval_f f1) (eval_f f2)
      | EQ f1 f2    => (eval_f f1) = (eval_f f2)
      end.

    Lemma eval_f_rew : forall b (f:GFormula b),
        eval_f f =
        match f in GFormula b' return rtyp b' with
        | TT tb => eTT tb
        | FF tb => eFF tb
        | A b a _ =>  ea b a
        | X p => ex  p
        | @AND b e1 e2 => eAND b (eval_f  e1) (eval_f e2)
        | @OR b e1 e2  => eOR b (eval_f e1) (eval_f e2)
        | @NOT b e     => eNOT b (eval_f e)
        | @IMPL b f1 _ f2 => eIMPL b (eval_f f1)  (eval_f f2)
        | @IFF b f1 f2    => eIFF b (eval_f f1) (eval_f f2)
        | EQ f1 f2    => (eval_f f1) = (eval_f f2)
        end.
    Proof.
      destruct f ; reflexivity.
    Qed.

  End EVAL.


  Definition hold (b : bool) : rtyp b ->  Prop :=
    if b as b0 return (rtyp b0 -> Prop) then fun x  => x else is_true.

  Definition eiff (b : bool) : rtyp b -> rtyp b -> Prop :=
    if b as b' return rtyp b' -> rtyp b' -> Prop then iff else @eq bool.

  Lemma eiff_refl : forall (b:bool) (x : rtyp b),
      eiff b x x.
  Proof.
    destruct b ; simpl; tauto.
  Qed.

  Lemma eiff_sym : forall b (x y : rtyp b), eiff b x y -> eiff b y x.
  Proof.
    destruct b ; simpl; intros ; intuition.
  Qed.

  Lemma eiff_trans : forall b (x y z : rtyp b), eiff b x y -> eiff b y z -> eiff b x z.
  Proof.
    destruct b ; simpl; intros ; intuition congruence.
  Qed.

  Lemma hold_eiff : forall (b : bool) (x y : rtyp b),
      (hold b x <-> hold b y) <-> eiff b x y.
  Proof.
    destruct b ; simpl.
    - tauto.
    - unfold is_true.
      destruct x,y ; intuition congruence.
  Qed.

  Instance eiff_eq (b:bool) : Equivalence (eiff b).
  Proof.
    constructor.
    - exact (eiff_refl b).
    - exact (eiff_sym b).
    - exact (eiff_trans b).
  Qed.

  Add Parametric Morphism (b:bool) : (@eAND b) with signature eiff b ==> eiff b ==> eiff b as eAnd_morph.
  Proof.
    intros.
    destruct b ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (b:bool) : (@eOR b) with signature eiff b ==> eiff b ==> eiff b as eOR_morph.
  Proof.
    intros.
    destruct b ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (b:bool) : (@eIMPL b) with signature eiff b ==> eiff b ==> eiff b as eIMPL_morph.
  Proof.
    intros.
    destruct b ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (b:bool) : (@eIFF b) with signature eiff b ==> eiff b ==> eiff b as eIFF_morph.
  Proof.
    intros.
    destruct b ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (b:bool) : (@eNOT b) with signature eiff b ==> eiff b as eNOT_morph.
  Proof.
    intros.
    destruct b ; simpl in *; intuition congruence.
  Qed.

  Lemma eval_f_morph :
    forall  (ev ev' : forall (b:bool), TA -> rtyp b),
      (forall b a, eiff b (ev b a) (ev' b a)) ->
      forall (b:bool)(f : GFormula b),
        (eiff b (eval_f ev f) (eval_f ev' f)).
  Proof.
    induction f ; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply H.
    - rewrite IHf1. rewrite IHf2. reflexivity.
    - rewrite IHf1. rewrite IHf2. reflexivity.
    - rewrite IHf. reflexivity.
    - rewrite IHf1. rewrite IHf2. reflexivity.
    - rewrite IHf1. rewrite IHf2. reflexivity.
    - simpl in *. intuition congruence.
  Qed.

End S.



(** Typical boolean formulae *)
Definition bProp (b:bool) := if b then Prop else bool.

Definition BFormula (A : Type) := @GFormula A bProp unit unit.

Section MAPATOMS.
  Context {TA TA':Type}.
  Context {TX  : bool -> Type}.
  Context {AA  : Type}.
  Context {AF  : Type}.


  Fixpoint map_bformula (b:bool)(fct : TA -> TA') (f : @GFormula TA TX AA AF b) : @GFormula TA' TX AA AF b:=
    match f with
    | TT b => TT b
    | FF b => FF b
    | X b p => X b p
    | A b a t => A b (fct a) t
    | AND f1 f2 => AND (map_bformula fct f1) (map_bformula fct f2)
    | OR f1 f2 => OR (map_bformula fct f1) (map_bformula fct f2)
    | NOT f     => NOT (map_bformula fct f)
    | IMPL f1 a f2 => IMPL (map_bformula fct f1) a (map_bformula fct f2)
    | IFF f1 f2 => IFF (map_bformula fct f1) (map_bformula fct f2)
    | EQ f1 f2  => EQ (map_bformula fct f1) (map_bformula fct f2)
    end.

End MAPATOMS.

Lemma map_simpl : forall A B f l, @map A B f l = match l with
                                                 | nil => nil
                                                 | a :: l=> (f a) :: (@map A B f l)
                                                 end.
Proof.
  destruct l ; reflexivity.
Qed.


Section S.
  (** A cnf tracking annotations of atoms. *)

  (** Type parameters *)
  Variable Env   : Type.
  Variable Term  : Type.
  Variable Term' : Type.
  Variable Annot : Type.

  Variable unsat : Term'  -> bool. (* see [unsat_prop] *)
  Variable deduce : Term' -> Term' -> option Term'. (* see [deduce_prop] *)

  Definition clause := list  (Term' * Annot).
  Definition cnf := list clause.

  Variable normalise : Term -> Annot -> cnf.
  Variable negate : Term -> Annot -> cnf.


  Definition cnf_tt : cnf := @nil clause.
  Definition cnf_ff : cnf :=  cons (@nil (Term' * Annot)) nil.

  (** Our cnf is optimised and detects contradictions on the fly. *)

  Fixpoint add_term (t: Term' * Annot) (cl : clause) : option clause :=
    match cl with
    | nil =>
      match deduce (fst t) (fst t) with
      | None =>  Some (t ::nil)
      | Some u => if unsat u then None else Some (t::nil)
      end
    | t'::cl =>
      match deduce (fst t) (fst t') with
      | None =>
        match add_term t cl with
        | None => None
        | Some cl' => Some (t' :: cl')
        end
      | Some u =>
        if unsat u then None else
          match add_term t cl with
          | None => None
          | Some cl' => Some (t' :: cl')
          end
      end
    end.

  Fixpoint or_clause (cl1 cl2 : clause) : option clause :=
    match cl1 with
    | nil => Some cl2
    | t::cl => match add_term t cl2 with
               | None => None
               | Some cl' => or_clause cl cl'
               end
    end.

  Definition xor_clause_cnf (t:clause) (f:cnf) : cnf :=
    List.fold_left (fun acc e =>
                      match or_clause t e with
                      | None => acc
                      | Some cl => cl :: acc
                      end) f nil .

  Definition or_clause_cnf (t: clause) (f:cnf) : cnf :=
    match t with
    | nil => f
    | _   => xor_clause_cnf t f
    end.


  Fixpoint or_cnf (f : cnf) (f' : cnf) {struct f}: cnf :=
    match f with
    | nil => cnf_tt
    | e :: rst => (or_cnf rst f') +++ (or_clause_cnf e f')
    end.


  Definition and_cnf (f1 : cnf) (f2 : cnf) : cnf :=
    f1 +++ f2.

  (** TX is Prop in Coq and EConstr.constr in Ocaml.
      AF is unit in Coq and Names.Id.t in Ocaml
   *)
  Definition TFormula (TX: bool -> Type) (AF: Type) := @GFormula Term TX Annot AF.


  Definition is_cnf_tt (c : cnf) : bool :=
    match c with
    | nil => true
    | _  => false
    end.

  Definition is_cnf_ff (c : cnf) : bool :=
    match c with
    | nil::nil => true
    | _        => false
    end.

  Definition and_cnf_opt (f1 : cnf) (f2 : cnf) : cnf :=
    if is_cnf_ff f1 || is_cnf_ff f2
    then cnf_ff
    else
      if is_cnf_tt f2
      then f1
      else and_cnf f1 f2.


  Definition or_cnf_opt (f1 : cnf) (f2 : cnf) : cnf :=
    if is_cnf_tt f1 || is_cnf_tt f2
    then cnf_tt
    else if is_cnf_ff f2
         then f1 else or_cnf f1 f2.

  Section REC.
    Context {TX : bool -> Type}.
    Context {AF : Type}.

    Variable REC : forall (pol : bool) (b:bool) (f : TFormula TX AF b), cnf.

    Definition mk_and (b:bool) (pol:bool) (f1 f2 : TFormula TX AF b):=
      (if pol then and_cnf_opt else or_cnf_opt) (REC pol f1) (REC pol f2).

    Definition mk_or (b:bool) (pol:bool) (f1 f2 : TFormula TX AF b):=
      (if pol then or_cnf_opt else and_cnf_opt) (REC pol f1) (REC pol f2).

    Definition mk_impl (b:bool) (pol:bool) (f1 f2 : TFormula TX AF b):=
      (if pol then or_cnf_opt else and_cnf_opt) (REC (negb pol) f1) (REC pol f2).


    Definition mk_iff (b:bool) (pol:bool) (f1 f2: TFormula TX AF b):=
      or_cnf_opt (and_cnf_opt (REC (negb pol) f1) (REC false f2))
                 (and_cnf_opt (REC pol f1) (REC true f2)).


  End REC.

  Definition is_bool {TX : bool -> Type} {AF: Type} (b:bool) (f : TFormula TX AF b) :=
    match f with
    | TT _ => Some true
    | FF _ => Some false
    | _    => None
    end.

  Lemma is_bool_inv : forall {TX : bool -> Type} {AF: Type} (b:bool) (f : TFormula  TX AF b) res,
      is_bool f = Some res -> f = if res then TT _ else FF _.
  Proof.
    intros.
    destruct f ; inversion H; reflexivity.
  Qed.


  Fixpoint xcnf {TX : bool -> Type} {AF: Type} (pol : bool) (b:bool) (f : TFormula TX AF b)  {struct f}: cnf :=
    match f with
    | TT b => if pol then cnf_tt else cnf_ff
    | FF b => if pol then cnf_ff else cnf_tt
    | X b p => if pol then cnf_ff else cnf_ff (* This is not complete - cannot negate any proposition *)
    | A b x t => if pol then normalise x  t else negate x  t
    | NOT e  => xcnf (negb pol) e
    | AND e1 e2 => mk_and xcnf pol e1 e2
    | OR e1 e2  => mk_or xcnf pol e1 e2
    | IMPL e1 _ e2 => mk_impl xcnf pol e1 e2
    | IFF e1 e2 => match is_bool e2 with
                   | Some isb => xcnf (if isb then pol else negb pol) e1
                   | None  => mk_iff xcnf pol e1 e2
                   end
    | EQ e1 e2 =>
      match is_bool e2 with
      | Some isb => xcnf (if isb then pol else negb pol) e1
      | None  => mk_iff xcnf pol e1 e2
      end
    end.

  Section CNFAnnot.

    (** Records annotations used to optimise the cnf.
          Those need to be kept when pruning the formula.
          For efficiency, this is a separate function.
     *)

    Fixpoint radd_term (t : Term' * Annot) (cl : clause) : clause + list Annot :=
      match cl with
      | nil => (* if t is unsat, the clause is empty BUT t is needed. *)
        match deduce (fst t) (fst t) with
        | Some u => if unsat u then inr ((snd t)::nil) else inl (t::nil)
        | None   => inl (t::nil)
        end
      | t'::cl => (* if t /\ t' is unsat, the clause is empty BUT t & t' are needed *)
        match deduce (fst t) (fst t') with
        | Some u => if unsat u then inr ((snd t)::(snd t')::nil)
                    else match radd_term t cl with
                         | inl cl' => inl (t'::cl')
                         | inr l   => inr l
                         end
        | None  => match radd_term t cl  with
                   | inl cl' => inl (t'::cl')
                   | inr l   => inr l
                   end
        end
      end.

    Fixpoint ror_clause cl1 cl2 :=
      match cl1 with
      | nil => inl cl2
      | t::cl => match radd_term t cl2 with
                 | inl cl' => ror_clause cl cl'
                 | inr l   => inr l
                 end
      end.

    Definition xror_clause_cnf t f :=
      List.fold_left (fun '(acc,tg) e  =>
                        match ror_clause t e with
                        | inl cl => (cl :: acc,tg)
                        | inr l => (acc,tg+++l)
                        end) f (nil,nil).

    Definition ror_clause_cnf t f :=
      match t with
      | nil => (f,nil)
      | _   => xror_clause_cnf t f
      end.


    Fixpoint ror_cnf (f f':list clause) :=
      match f with
      | nil => (cnf_tt,nil)
      | e :: rst =>
        let (rst_f',t) := ror_cnf rst f' in
        let (e_f', t') := ror_clause_cnf e f' in
        (rst_f' +++ e_f', t +++ t')
      end.

    Definition annot_of_clause (l : clause) : list Annot :=
      List.map snd l.

    Definition annot_of_cnf (f : cnf) : list Annot :=
      List.fold_left (fun acc e => annot_of_clause e +++ acc ) f nil.


    Definition ror_cnf_opt f1 f2 :=
      if is_cnf_tt f1
      then (cnf_tt ,  nil)
      else if is_cnf_tt f2
           then (cnf_tt, nil)
           else if is_cnf_ff f2
                then (f1,nil)
                else ror_cnf f1 f2.


    Definition ocons {A : Type} (o : option A) (l : list A) : list A :=
      match o with
      | None => l
      | Some e => e ::l
      end.

    Definition ratom (c : cnf) (a : Annot) : cnf * list Annot :=
      if is_cnf_ff c || is_cnf_tt c
      then (c,a::nil)
      else (c,nil). (* t is embedded in c *)

    Section REC.
      Context {TX : bool -> Type} {AF : Type}.

      Variable RXCNF : forall (polarity: bool) (b:bool) (f: TFormula TX AF b) , cnf * list Annot.

      Definition rxcnf_and (polarity:bool) (b : bool) (e1 e2 : TFormula TX AF b) :=
        let '(e1,t1) := RXCNF polarity e1 in
        let '(e2,t2) := RXCNF polarity e2 in
        if polarity
        then  (and_cnf_opt e1  e2, t1 +++ t2)
        else let (f',t') := ror_cnf_opt e1 e2 in
             (f', t1 +++ t2 +++ t').

      Definition rxcnf_or (polarity:bool) (b : bool) (e1 e2 : TFormula TX AF b) :=
        let '(e1,t1) := RXCNF polarity e1 in
        let '(e2,t2) := RXCNF polarity e2 in
        if polarity
        then let (f',t') := ror_cnf_opt e1 e2 in
             (f', t1 +++ t2 +++ t')
        else (and_cnf_opt e1 e2, t1 +++ t2).

      Definition rxcnf_impl (polarity:bool) (b : bool) (e1 e2 : TFormula TX AF b) :=
        let '(e1 , t1) := (RXCNF (negb polarity) e1) in
        if polarity
        then
          if is_cnf_ff e1
          then
            RXCNF polarity e2
          else (* compute disjunction *)
            let '(e2 , t2) := (RXCNF polarity e2) in
            let (f',t') := ror_cnf_opt e1 e2 in
            (f', t1 +++ t2 +++ t') (* record the hypothesis *)
        else
          let '(e2 , t2) := (RXCNF polarity e2) in
          (and_cnf_opt e1 e2, t1 +++ t2).

      Definition rxcnf_iff (polarity:bool) (b : bool) (e1 e2 : TFormula TX AF b) :=
        let '(c1,t1) := RXCNF (negb polarity) e1 in
        let '(c2,t2) := RXCNF false e2 in
        let '(c3,t3) := RXCNF polarity e1 in
        let '(c4,t4) := RXCNF true e2 in
        let (f',t') := ror_cnf_opt (and_cnf_opt c1 c2) (and_cnf_opt c3 c4) in
        (f', t1+++ t2+++t3 +++ t4 +++ t')
      .

    End REC.

    Fixpoint rxcnf {TX : bool -> Type} {AF: Type}(polarity : bool) (b:bool) (f : TFormula TX AF b) : cnf * list Annot :=

      match f with
      | TT _ => if polarity then (cnf_tt,nil) else (cnf_ff,nil)
      | FF _  => if polarity then (cnf_ff,nil) else (cnf_tt,nil)
      | X b p => if polarity then (cnf_ff,nil) else (cnf_ff,nil)
      | A b x t  => ratom (if polarity then normalise x t else negate x t) t
      | NOT e  => rxcnf (negb polarity) e
      | AND e1 e2 => rxcnf_and rxcnf polarity e1 e2
      | OR e1 e2  => rxcnf_or rxcnf polarity e1 e2
      | IMPL e1 a e2 => rxcnf_impl rxcnf polarity e1 e2
      | IFF e1 e2 => rxcnf_iff rxcnf polarity e1 e2
      | EQ e1 e2  => rxcnf_iff rxcnf polarity e1 e2
      end.

    Section Abstraction.
      Variable TX : bool -> Type.
      Variable AF : Type.

      Class to_constrT : Type :=
        {
          mkTT   : forall (b:bool), TX b;
          mkFF   : forall (b:bool), TX b;
          mkA    : forall (b:bool), Term -> Annot -> TX b;
          mkAND  : forall (b:bool), TX b -> TX b -> TX b;
          mkOR   : forall (b:bool), TX b -> TX b -> TX b;
          mkIMPL : forall (b:bool), TX b -> TX b -> TX b;
          mkIFF  : forall (b:bool), TX b -> TX b -> TX b;
          mkNOT  : forall (b:bool), TX b -> TX b;
          mkEQ   : TX false -> TX false -> TX true

        }.

      Context {to_constr : to_constrT}.

      Fixpoint aformula (b:bool) (f : TFormula TX AF b) : TX b :=
        match f with
        | TT b => mkTT b
        | FF b => mkFF b
        | X b p => p
        | A b x t => mkA b x t
        | AND f1 f2 => mkAND  (aformula f1) (aformula f2)
        | OR  f1 f2 => mkOR (aformula f1) (aformula f2)
        | IMPL f1 o f2 => mkIMPL  (aformula f1) (aformula f2)
        | IFF f1 f2 => mkIFF  (aformula f1) (aformula f2)
        | NOT f     => mkNOT  (aformula f)
        | EQ f1 f2  => mkEQ (aformula f1) (aformula f2)
        end.


      Definition is_X (b:bool) (f : TFormula TX AF b) : option (TX b) :=
        match f with
        | X b p => Some p
        | _   => None
        end.

      Definition is_X_inv : forall (b:bool) (f: TFormula TX AF b) x,
          is_X f = Some x -> f = X b x.
      Proof.
        destruct f ; simpl ; try congruence.
      Qed.

      Variable needA : Annot -> bool.

      Definition abs_and (b:bool) (f1 f2 : TFormula TX AF b)
                 (c : forall (b:bool), TFormula TX AF b -> TFormula TX AF b -> TFormula TX AF b) :=
        match is_X f1 , is_X f2 with
        | Some _  , _ | _ , Some _ => X b (aformula  (c b f1  f2))
        |   _     , _ => c b f1 f2
        end.

      Definition abs_or (b:bool) (f1 f2 : TFormula TX AF b)
                 (c : forall (b:bool), TFormula TX AF b -> TFormula TX AF b -> TFormula TX AF b) :=
        match is_X f1 , is_X f2 with
        | Some _  , Some _ => X b (aformula (c b f1  f2))
        |   _     , _ => c b f1 f2
        end.

      Definition abs_not (b : bool) (f1 : TFormula TX AF b)
                 (c : forall (b:bool), TFormula TX AF b -> TFormula TX AF b) :=
        match is_X f1 with
        | Some _   => X b (aformula (c b f1 ))
        |   _  => c b f1
        end.


      Definition mk_arrow (o : option AF) (b:bool) (f1 f2: TFormula TX AF b) :=
        match o with
        | None => IMPL f1 None f2
        | Some _ => if is_X f1 then f2 else IMPL f1 o f2
        end.

      Fixpoint abst_simpl  (b:bool) (f : TFormula TX AF b) : TFormula TX AF b:=
        match f  with
        | TT b => TT b
        | FF b =>  FF b
        | X b p => X b p
        | A b x t => if needA t then A b x t else X b (mkA b x t)
        | AND f1 f2 => AND (abst_simpl f1) (abst_simpl f2)
        | OR f1 f2 =>  OR (abst_simpl f1) (abst_simpl f2)
        | IMPL f1 o f2 => IMPL (abst_simpl f1) o (abst_simpl f2)
        | NOT f => NOT (abst_simpl f)
        | IFF f1 f2 => IFF (abst_simpl f1) (abst_simpl f2)
        | EQ f1 f2  => EQ (abst_simpl f1) (abst_simpl f2)
        end.

      Section REC.
        Variable REC : forall (pol : bool) (b:bool) (f : TFormula TX AF b), TFormula TX AF b.

        Definition abst_and (pol : bool) (b:bool) (f1 f2:TFormula TX AF b) : TFormula TX AF b:=
          (if pol then abs_and else abs_or) b (REC pol f1) (REC pol f2) AND.

        Definition abst_or (pol : bool) (b:bool) (f1 f2:TFormula TX AF b) : TFormula TX AF b:=
          (if pol then abs_or else abs_and) b (REC pol f1) (REC pol f2) OR.

        Definition abst_impl (pol : bool) (o :option AF) (b:bool) (f1 f2:TFormula TX AF b) : TFormula TX AF b:=
          (if pol then abs_or else abs_and) b (REC (negb pol) f1) (REC pol f2) (mk_arrow o).



        Definition or_is_X (b: bool) (f1 f2: TFormula TX AF b) : bool :=
          match is_X f1 , is_X f2 with
          | Some _ , _
          | _ , Some _ => true
          |  _ , _     => false
          end.

        Definition abs_iff  (b:bool) (nf1  ff2 f1 tf2 : TFormula TX AF b) (r:bool) (def : TFormula TX AF r) : TFormula TX AF r :=
          if andb (or_is_X nf1 ff2) (or_is_X f1 tf2)
          then X r (aformula def)
          else def.


        Definition abst_iff (pol : bool) (b:bool) (f1 f2: TFormula TX AF b) : TFormula TX AF b :=
          abs_iff   (REC (negb pol) f1) (REC false f2) (REC pol f1) (REC true f2) (IFF (abst_simpl f1) (abst_simpl f2)).

        Definition abst_eq (pol : bool)  (f1 f2: TFormula TX AF false) : TFormula TX AF true :=
          abs_iff   (REC (negb pol) f1) (REC false f2) (REC pol f1) (REC true f2) (EQ (abst_simpl f1) (abst_simpl f2)).

      End REC.

      Fixpoint abst_form  (pol : bool) (b:bool) (f : TFormula TX AF b) : TFormula TX AF b:=
        match f  with
        | TT b => if pol then TT b else X b (mkTT b)
        | FF b => if pol then X b (mkFF b) else FF b
        | X b p => X b p
        | A b x t => if needA t then A b x t else X b (mkA b x t)
        | AND f1 f2 => abst_and abst_form pol f1 f2
        | OR f1 f2 =>  abst_or abst_form pol f1 f2
        | IMPL f1 o f2 => abst_impl abst_form pol o f1 f2
        | NOT f => abs_not  (abst_form (negb pol) f) NOT
        | IFF f1 f2 => abst_iff abst_form  pol f1 f2
        | EQ f1 f2  => abst_eq abst_form pol f1 f2
        end.

      Lemma if_same : forall {A: Type} (b:bool) (t:A),
          (if b then t else t) = t.
      Proof.
        destruct b ; reflexivity.
      Qed.

      Lemma is_cnf_tt_cnf_ff :
        is_cnf_tt cnf_ff = false.
      Proof.
        reflexivity.
      Qed.

      Lemma is_cnf_ff_cnf_ff :
        is_cnf_ff cnf_ff = true.
      Proof.
        reflexivity.
      Qed.


      Lemma is_cnf_tt_inv : forall f1,
          is_cnf_tt f1 = true -> f1 = cnf_tt.
      Proof.
        unfold cnf_tt.
        destruct f1 ; simpl ; try congruence.
      Qed.

      Lemma is_cnf_ff_inv : forall f1,
          is_cnf_ff f1 = true -> f1 = cnf_ff.
      Proof.
        unfold cnf_ff.
        destruct f1 ; simpl ; try congruence.
        destruct c ; simpl ; try congruence.
        destruct f1 ; try congruence.
        reflexivity.
      Qed.


      Lemma if_cnf_tt : forall f, (if is_cnf_tt f then cnf_tt else f) = f.
      Proof.
        intros.
        destruct (is_cnf_tt f) eqn:EQ.
        apply is_cnf_tt_inv in EQ;auto.
        reflexivity.
      Qed.

      Lemma or_cnf_opt_cnf_ff : forall f,
          or_cnf_opt cnf_ff f = f.
      Proof.
        intros.
        unfold or_cnf_opt.
        rewrite is_cnf_tt_cnf_ff.
        simpl.
        destruct (is_cnf_tt f) eqn:EQ.
        apply is_cnf_tt_inv in EQ.
        congruence.
        destruct (is_cnf_ff f) eqn:EQ1.
        apply is_cnf_ff_inv in EQ1.
        congruence.
        reflexivity.
      Qed.

      Lemma abs_and_pol : forall (b:bool) (f1 f2: TFormula TX AF b) pol,
          and_cnf_opt (xcnf pol f1) (xcnf pol f2) =
          xcnf pol (abs_and f1 f2 (if pol then AND else OR)).
      Proof.
        unfold abs_and; intros.
        destruct (is_X f1) eqn:EQ1.
        apply is_X_inv in EQ1.
        subst.
        simpl.
        rewrite if_same. reflexivity.
        destruct (is_X f2) eqn:EQ2.
        apply is_X_inv in EQ2.
        subst.
        simpl.
        rewrite if_same.
        unfold and_cnf_opt.
        rewrite orb_comm. reflexivity.
        destruct pol ; simpl; auto.
      Qed.

      Lemma abs_or_pol : forall (b:bool) (f1 f2:TFormula TX AF b) pol,
          or_cnf_opt (xcnf pol f1) (xcnf pol f2) =
          xcnf pol (abs_or f1 f2 (if pol then OR else AND)).
      Proof.
        unfold abs_or; intros.
        destruct (is_X f1) eqn:EQ1.
        apply is_X_inv in EQ1.
        subst.
        destruct (is_X f2) eqn:EQ2.
        apply is_X_inv in EQ2.
        subst.
        simpl.
        rewrite if_same.
        reflexivity.
        simpl.
        rewrite if_same.
        destruct pol ; simpl; auto.
        destruct pol ; simpl ; auto.
      Qed.

      Variable needA_all : forall a, needA a = true.

      Lemma xcnf_true_mk_arrow_l : forall b o t (f:TFormula TX AF b),
          xcnf true (mk_arrow o (X b t) f) = xcnf true f.
      Proof.
        destruct o ; simpl; auto.
        intros. rewrite or_cnf_opt_cnf_ff. reflexivity.
      Qed.

      Lemma or_cnf_opt_cnf_ff_r : forall f,
          or_cnf_opt f  cnf_ff = f.
      Proof.
        unfold or_cnf_opt.
        intros.
        rewrite is_cnf_tt_cnf_ff.
        rewrite orb_comm.
        simpl.
        apply if_cnf_tt.
      Qed.

      Lemma xcnf_true_mk_arrow_r : forall b o t (f:TFormula TX AF b),
          xcnf true (mk_arrow o  f (X b t)) = xcnf false f.
      Proof.
        destruct o ; simpl; auto.
        - intros.
          destruct (is_X f) eqn:EQ.
          apply is_X_inv in EQ. subst. reflexivity.
          simpl.
          apply or_cnf_opt_cnf_ff_r.
        - intros.
          apply or_cnf_opt_cnf_ff_r.
      Qed.

      Lemma and_cnf_opt_cnf_ff_r : forall f,
          and_cnf_opt f cnf_ff = cnf_ff.
      Proof.
        intros.
        unfold and_cnf_opt.
        rewrite is_cnf_ff_cnf_ff.
        rewrite orb_comm. reflexivity.
      Qed.

      Lemma and_cnf_opt_cnf_ff : forall f,
          and_cnf_opt cnf_ff f  = cnf_ff.
      Proof.
        intros.
        unfold and_cnf_opt.
        rewrite is_cnf_ff_cnf_ff.
        reflexivity.
      Qed.


      Lemma and_cnf_opt_cnf_tt : forall f,
          and_cnf_opt f cnf_tt   = f.
      Proof.
        intros.
        unfold and_cnf_opt.
        simpl. rewrite orb_comm.
        simpl.
        destruct (is_cnf_ff f) eqn:EQ ; auto.
        apply is_cnf_ff_inv in EQ.
        auto.
      Qed.

      Lemma is_bool_abst_simpl : forall b (f:TFormula TX AF b),
          is_bool (abst_simpl f) = is_bool f.
      Proof.
        induction f ; simpl ; auto.
        rewrite needA_all.
        reflexivity.
      Qed.

      Lemma abst_simpl_correct : forall b (f:TFormula TX AF b) pol,
          xcnf pol f = xcnf pol (abst_simpl f).
      Proof.
        induction f; simpl;intros;
          unfold mk_and,mk_or,mk_impl, mk_iff;
          rewrite <- ?IHf;
          try (rewrite <- !IHf1; rewrite <- !IHf2);
          try reflexivity.
        - rewrite needA_all.
          reflexivity.
        - rewrite is_bool_abst_simpl.
          destruct (is_bool f2); auto.
        - rewrite is_bool_abst_simpl.
          destruct (is_bool f2); auto.
      Qed.

      Ltac is_X :=
        match goal with
        | |-context[is_X ?X] =>
          let f := fresh "EQ" in
          destruct (is_X X) eqn:f ;
          [apply is_X_inv in f|]
        end.

      Ltac cnf_simpl :=
        repeat match goal with
               | |- context[and_cnf_opt cnf_ff _ ] => rewrite and_cnf_opt_cnf_ff
               | |- context[and_cnf_opt _ cnf_ff] => rewrite and_cnf_opt_cnf_ff_r
               | |- context[and_cnf_opt _ cnf_tt] => rewrite and_cnf_opt_cnf_tt
               | |- context[or_cnf_opt cnf_ff _] => rewrite or_cnf_opt_cnf_ff
               | |- context[or_cnf_opt _ cnf_ff] => rewrite or_cnf_opt_cnf_ff_r
               end.

      Lemma or_is_X_inv : forall (b:bool) (f1 f2 : TFormula TX AF b),
          or_is_X f1 f2 = true ->
          exists b1, is_X f1 = Some b1 \/ is_X f2 = Some b1.
      Proof.
        unfold or_is_X.
        intros b f1 f2.
        repeat is_X.
        exists t ; intuition.
        exists t ; intuition.
        exists t ; intuition.
        congruence.
      Qed.

      Lemma mk_iff_is_bool : forall (b:bool) (f1 f2:TFormula TX AF b) pol,
          match is_bool f2 with
          | Some isb => xcnf (if isb then pol else negb pol) f1
          | None => mk_iff xcnf pol f1 f2
          end = mk_iff xcnf pol f1 f2.
      Proof.
        intros.
        destruct (is_bool f2) eqn:EQ; auto.
        apply is_bool_inv in EQ.
        subst.
        unfold mk_iff.
        destruct b0 ; simpl; cnf_simpl; reflexivity.
      Qed.

      Lemma abst_iff_correct : forall
          (b : bool)
          (f1 f2 : GFormula b)
          (IHf1 : forall pol : bool, xcnf pol f1 = xcnf pol (abst_form pol f1))
          (IHf2 : forall pol : bool, xcnf pol f2 = xcnf pol (abst_form pol f2))
          (pol : bool),
          xcnf pol (IFF f1 f2) = xcnf pol (abst_iff abst_form pol f1 f2).
      Proof.
        intros; simpl.
        assert (D1 :mk_iff xcnf pol f1 f2 = mk_iff xcnf pol (abst_simpl f1) (abst_simpl f2)).
        {
          simpl.
          unfold mk_iff.
          rewrite <- !abst_simpl_correct.
          reflexivity.
        }
        rewrite mk_iff_is_bool.
        unfold abst_iff,abs_iff.
        destruct (      or_is_X (abst_form (negb pol) f1) (abst_form false f2) &&
                                or_is_X (abst_form pol f1) (abst_form true f2)
                 ) eqn:EQ1.
        + simpl.
          rewrite andb_true_iff in EQ1.
          destruct EQ1 as (EQ1 & EQ2).
          apply or_is_X_inv in EQ1.
          apply or_is_X_inv in EQ2.
          destruct EQ1 as (b1 & EQ1).
          destruct EQ2 as (b2 & EQ2).
          rewrite if_same.
          unfold mk_iff.
          rewrite !IHf1.
          rewrite !IHf2.
          destruct EQ1 as [EQ1 | EQ1] ; apply is_X_inv in EQ1;
            destruct EQ2 as [EQ2 | EQ2] ; apply is_X_inv in EQ2;
              rewrite EQ1; rewrite EQ2; simpl;
                repeat rewrite if_same ; cnf_simpl; auto.
        + simpl.
          rewrite mk_iff_is_bool.
          unfold mk_iff.
          rewrite <- ! abst_simpl_correct.
          reflexivity.
      Qed.

      Lemma abst_eq_correct : forall
          (f1 f2 : GFormula false)
          (IHf1 : forall pol : bool, xcnf pol f1 = xcnf pol (abst_form pol f1))
          (IHf2 : forall pol : bool, xcnf pol f2 = xcnf pol (abst_form pol f2))
          (pol : bool),
          xcnf pol (EQ f1 f2) = xcnf pol (abst_form pol (EQ f1 f2)).
      Proof.
        intros.
        change (xcnf pol (IFF f1 f2) = xcnf pol (abst_form pol (EQ f1 f2))).
        rewrite abst_iff_correct by assumption.
        simpl. unfold abst_iff, abst_eq.
        unfold abs_iff.
        destruct (or_is_X (abst_form (negb pol) f1) (abst_form false f2) &&
                          or_is_X (abst_form pol f1) (abst_form true f2)
                 ) ; auto.
      Qed.


      Lemma abst_form_correct : forall b (f:TFormula TX AF b) pol,
          xcnf pol f = xcnf pol (abst_form pol f).
      Proof.
        induction f;intros.
        - simpl. destruct pol ; reflexivity.
        - simpl. destruct pol ; reflexivity.
        - simpl. reflexivity.
        - simpl. rewrite needA_all.
          reflexivity.
        - simpl. unfold mk_and.
          specialize (IHf1 pol).
          specialize (IHf2 pol).
          rewrite IHf1.
          rewrite IHf2.
          destruct pol.
          + apply abs_and_pol; auto.
          + apply abs_or_pol.
        - simpl. unfold mk_or.
          specialize (IHf1 pol).
          specialize (IHf2 pol).
          rewrite IHf1.
          rewrite IHf2.
          destruct pol.
          + apply abs_or_pol; auto.
          + apply abs_and_pol; auto.
        -  simpl.
           unfold abs_not.
           specialize (IHf (negb pol)).
           destruct (is_X (abst_form (negb pol) f)) eqn:EQ1.
           + apply is_X_inv in EQ1.
             rewrite EQ1 in *.
             simpl in *.
             destruct pol ; auto.
           + simpl. congruence.
        - simpl. unfold mk_impl.
          specialize (IHf1 (negb pol)).
          specialize (IHf2 pol).
          destruct pol.
          +
            simpl in *.
            unfold abs_or.
            destruct (is_X (abst_form false f1)) eqn:EQ1;
              destruct (is_X (abst_form true f2)) eqn:EQ2 ; simpl.
            * apply is_X_inv in EQ1.
              apply is_X_inv in EQ2.
              rewrite EQ1 in *.
              rewrite EQ2 in *.
              rewrite IHf1. rewrite IHf2.
              simpl. reflexivity.
            * apply is_X_inv in EQ1.
              rewrite EQ1 in *.
              rewrite IHf1.
              simpl.
              rewrite xcnf_true_mk_arrow_l.
              rewrite or_cnf_opt_cnf_ff.
              congruence.
            * apply is_X_inv in EQ2.
              rewrite EQ2 in *.
              rewrite IHf2.
              simpl.
              rewrite xcnf_true_mk_arrow_r.
              rewrite or_cnf_opt_cnf_ff_r.
              congruence.
            * destruct o ; simpl ; try congruence.
              rewrite EQ1.
              simpl. congruence.
          +  simpl in *.
             unfold abs_and.
             destruct (is_X (abst_form true f1)) eqn:EQ1;
               destruct (is_X (abst_form false f2)) eqn:EQ2 ; simpl.
             * apply is_X_inv in EQ1.
               apply is_X_inv in EQ2.
               rewrite EQ1 in *.
               rewrite EQ2 in *.
               rewrite IHf1. rewrite IHf2.
               simpl. reflexivity.
             * apply is_X_inv in EQ1.
               rewrite EQ1 in *.
               rewrite IHf1.
               simpl. reflexivity.
             * apply is_X_inv in EQ2.
               rewrite EQ2 in *.
               rewrite IHf2.
               simpl. unfold and_cnf_opt.
               rewrite orb_comm. reflexivity.
             * destruct o; simpl.
               rewrite EQ1. simpl.
               congruence.
               congruence.
        -  apply abst_iff_correct; auto.
        -  apply abst_eq_correct; auto.
      Qed.

    End Abstraction.


  End CNFAnnot.


  Lemma radd_term_term : forall a' a cl, radd_term a a' = inl cl -> add_term a a' = Some cl.
  Proof.
    induction a' ; simpl.
    - intros.
      destruct (deduce (fst a) (fst a)).
      destruct (unsat t). congruence.
      inversion H. reflexivity.
      inversion H ;reflexivity.
    - intros.
      destruct (deduce (fst a0) (fst a)).
      destruct (unsat t). congruence.
      destruct (radd_term a0 a') eqn:RADD; try congruence.
      inversion H. subst.
      apply IHa' in RADD.
      rewrite RADD.
      reflexivity.
      destruct (radd_term a0 a') eqn:RADD; try congruence.
      inversion H. subst.
      apply IHa' in RADD.
      rewrite RADD.
      reflexivity.
  Qed.

  Lemma radd_term_term' : forall a' a cl, add_term a a' = Some cl -> radd_term a a' = inl cl.
  Proof.
    induction a' ; simpl.
    - intros.
      destruct (deduce (fst a) (fst a)).
      destruct (unsat t). congruence.
      inversion H. reflexivity.
      inversion H ;reflexivity.
    - intros.
      destruct (deduce (fst a0) (fst a)).
      destruct (unsat t). congruence.
      destruct (add_term a0 a') eqn:RADD; try congruence.
      inversion H. subst.
      apply IHa' in RADD.
      rewrite RADD.
      reflexivity.
      destruct (add_term a0 a') eqn:RADD; try congruence.
      inversion H. subst.
      apply IHa' in RADD.
      rewrite RADD.
      reflexivity.
  Qed.

  Lemma xror_clause_clause : forall a f,
      fst (xror_clause_cnf a f) = xor_clause_cnf a f.
  Proof.
    unfold xror_clause_cnf.
    unfold xor_clause_cnf.
    assert (ACC: fst (@nil clause,@nil Annot) = nil).
    reflexivity.
    intros.
    set (F1:= (fun '(acc, tg) (e : clause) =>
                 match ror_clause a e with
                 | inl cl => (cl :: acc, tg)
                 | inr l => (acc, tg +++ l)
                 end)).
    set (F2:= (fun (acc : list clause) (e : clause) =>
                 match or_clause a e with
                 | Some cl => cl :: acc
                 | None => acc
                 end)).
    revert ACC.
    generalize (@nil clause,@nil Annot).
    generalize (@nil clause).
    induction f ; simpl ; auto.
    intros.
    apply IHf.
    unfold F1 , F2.
    destruct p ; simpl in * ; subst.
    clear.
    revert a0.
    induction a; simpl; auto.
    intros.
    destruct (radd_term a a1) eqn:RADD.
    apply radd_term_term in RADD.
    rewrite RADD.
    auto.
    destruct (add_term a a1) eqn:RADD'.
    apply radd_term_term' in RADD'.
    congruence.
    reflexivity.
  Qed.

  Lemma ror_clause_clause : forall a f,
      fst (ror_clause_cnf a f) = or_clause_cnf a f.
  Proof.
    unfold ror_clause_cnf,or_clause_cnf.
    destruct a ; auto.
    apply xror_clause_clause.
  Qed.

  Lemma ror_cnf_cnf : forall f1 f2, fst (ror_cnf f1 f2) = or_cnf f1 f2.
  Proof.
    induction f1 ; simpl ; auto.
    intros.
    specialize (IHf1  f2).
    destruct(ror_cnf f1 f2).
    rewrite <- ror_clause_clause.
    destruct(ror_clause_cnf a f2).
    simpl.
    rewrite <- IHf1.
    reflexivity.
  Qed.

  Lemma ror_opt_cnf_cnf : forall f1 f2, fst (ror_cnf_opt f1 f2) = or_cnf_opt f1 f2.
  Proof.
    unfold ror_cnf_opt, or_cnf_opt.
    intros.
    destruct (is_cnf_tt f1).
    - simpl ; auto.
    - simpl. destruct (is_cnf_tt f2) ; simpl ; auto.
      destruct (is_cnf_ff f2) eqn:EQ.
      reflexivity.
      apply ror_cnf_cnf.
  Qed.

  Lemma ratom_cnf : forall  f a,
      fst (ratom f a) = f.
  Proof.
    unfold ratom.
    intros.
    destruct (is_cnf_ff f || is_cnf_tt f); auto.
  Qed.

  Lemma rxcnf_and_xcnf : forall {TX : bool -> Type} {AF:Type} (b:bool) (f1 f2:TFormula TX AF b)
                                (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
                                (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
      forall pol : bool, fst (rxcnf_and rxcnf pol f1 f2) = mk_and xcnf pol f1 f2.
  Proof.
    intros.
    unfold mk_and, rxcnf_and.
    specialize (IHf1 pol).
    specialize (IHf2 pol).
    destruct (rxcnf pol f1).
    destruct (rxcnf pol f2).
    simpl in *.
    subst. destruct pol ; auto.
    rewrite <- ror_opt_cnf_cnf.
    destruct (ror_cnf_opt (xcnf false f1) (xcnf false f2)).
    reflexivity.
  Qed.

  Lemma rxcnf_or_xcnf :
    forall {TX : bool -> Type} {AF:Type} (b:bool) (f1 f2:TFormula TX AF b)
           (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
           (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
    forall pol : bool, fst (rxcnf_or rxcnf pol f1 f2) = mk_or xcnf pol f1 f2.
  Proof.
    intros.
    unfold rxcnf_or, mk_or.
    specialize (IHf1 pol).
    specialize (IHf2 pol).
    destruct (rxcnf pol f1).
    destruct (rxcnf pol f2).
    simpl in *.
    subst. destruct pol ; auto.
    rewrite <- ror_opt_cnf_cnf.
    destruct (ror_cnf_opt (xcnf true f1) (xcnf true f2)).
    reflexivity.
  Qed.

  Lemma rxcnf_impl_xcnf :
    forall {TX : bool -> Type} {AF:Type} (b:bool) (f1 f2:TFormula TX AF b)
           (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
           (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
    forall pol : bool, fst (rxcnf_impl rxcnf pol f1 f2) = mk_impl xcnf pol f1 f2.
  Proof.
    intros.
    unfold rxcnf_impl, mk_impl, mk_or.
    specialize (IHf1 (negb pol)).
    specialize (IHf2 pol).
    rewrite <- IHf1.
    rewrite <- IHf2.
    destruct (rxcnf (negb pol) f1).
    destruct (rxcnf pol f2).
    simpl in *.
    subst.
    destruct pol;auto.
    generalize (is_cnf_ff_inv (xcnf (negb true) f1)).
    destruct (is_cnf_ff (xcnf (negb true) f1)).
    + intros.
      rewrite H by auto.
      unfold or_cnf_opt.
      simpl.
      destruct (is_cnf_tt (xcnf true f2)) eqn:EQ;auto.
      apply is_cnf_tt_inv in EQ; auto.
      destruct (is_cnf_ff (xcnf true f2)) eqn:EQ1.
      apply is_cnf_ff_inv in EQ1. congruence.
      reflexivity.
    +
      rewrite <- ror_opt_cnf_cnf.
      destruct (ror_cnf_opt (xcnf (negb true) f1) (xcnf true f2)).
      intros.
      reflexivity.
  Qed.




  Lemma rxcnf_iff_xcnf :
    forall {TX : bool -> Type} {AF:Type} (b:bool) (f1 f2:TFormula TX AF b)
           (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
           (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
    forall pol : bool, fst (rxcnf_iff rxcnf pol f1 f2) = mk_iff xcnf pol f1 f2.
  Proof.
    intros.
    unfold rxcnf_iff.
    unfold mk_iff.
    rewrite <- (IHf1 (negb pol)).
    rewrite <- (IHf1 pol).
    rewrite <- (IHf2 false).
    rewrite <- (IHf2 true).
    destruct (rxcnf (negb pol) f1).
    destruct (rxcnf false f2).
    destruct (rxcnf pol f1).
    destruct (rxcnf true f2).
    destruct (ror_cnf_opt (and_cnf_opt c c0) (and_cnf_opt c1 c2)) eqn:EQ.
    simpl.
    change c3 with (fst (c3,l3)).
    rewrite <- EQ. rewrite ror_opt_cnf_cnf.
    reflexivity.
  Qed.

  Lemma rxcnf_xcnf : forall {TX : bool -> Type} {AF:Type} (b:bool) (f:TFormula TX AF b) pol,
      fst (rxcnf  pol f) = xcnf pol f.
  Proof.
    induction f ; simpl ; auto.
    - destruct pol; simpl ; auto.
    - destruct pol; simpl ; auto.
    - destruct pol ; simpl ; auto.
    - intros. rewrite ratom_cnf. reflexivity.
    - apply rxcnf_and_xcnf; auto.
    - apply rxcnf_or_xcnf; auto.
    - apply rxcnf_impl_xcnf; auto.
    - intros.
      rewrite mk_iff_is_bool.
      apply rxcnf_iff_xcnf; auto.
    - intros.
      rewrite mk_iff_is_bool.
      apply rxcnf_iff_xcnf; auto.
  Qed.


  Variable eval'  : Env -> Term' -> Prop.

  Variable no_middle_eval' : forall env d, (eval' env d) \/ ~ (eval' env d).

  Variable unsat_prop : forall t, unsat t  = true ->
                                  forall env, eval' env t -> False.

  Variable deduce_prop : forall t t' u,
      deduce t t' = Some u -> forall env,
        eval' env t -> eval' env t' -> eval' env u.

  Definition eval_tt (env : Env) (tt : Term' * Annot) := eval' env (fst tt).

  Definition eval_clause (env : Env) (cl : clause) := ~ make_conj  (eval_tt env) cl.

  Definition eval_cnf (env : Env) (f:cnf) := make_conj  (eval_clause  env) f.

  Lemma eval_cnf_app : forall env x y, eval_cnf env (x+++y) <-> eval_cnf env x /\ eval_cnf env y.
  Proof.
    unfold eval_cnf.
    intros.
    rewrite make_conj_rapp.
    rewrite make_conj_app ; auto.
    tauto.
  Qed.

  Lemma eval_cnf_ff : forall env, eval_cnf env cnf_ff <-> False.
  Proof.
    unfold cnf_ff, eval_cnf,eval_clause.
    simpl. tauto.
  Qed.

  Lemma eval_cnf_tt : forall env, eval_cnf env cnf_tt <-> True.
  Proof.
    unfold cnf_tt, eval_cnf,eval_clause.
    simpl. tauto.
  Qed.

  Lemma eval_cnf_and_opt : forall env x y, eval_cnf env (and_cnf_opt x y) <-> eval_cnf env (and_cnf x y).
  Proof.
    unfold and_cnf_opt.
    intros.
    destruct (is_cnf_ff x) eqn:F1.
    { apply is_cnf_ff_inv in F1.
      simpl. subst.
      unfold and_cnf.
      rewrite eval_cnf_app.
      rewrite eval_cnf_ff.
      tauto.
    }
    simpl.
    destruct (is_cnf_ff y) eqn:F2.
    { apply is_cnf_ff_inv in F2.
      simpl. subst.
      unfold and_cnf.
      rewrite eval_cnf_app.
      rewrite eval_cnf_ff.
      tauto.
    }
    destruct (is_cnf_tt y) eqn:F3.
    {
      apply is_cnf_tt_inv in F3.
      subst.
      unfold and_cnf.
      rewrite eval_cnf_app.
      rewrite eval_cnf_tt.
      tauto.
    }
    tauto.
  Qed.

  Definition eval_opt_clause (env : Env) (cl: option clause) :=
    match cl with
    | None => True
    | Some cl => eval_clause env cl
    end.

  Lemma add_term_correct : forall env t cl , eval_opt_clause env (add_term t cl) <-> eval_clause env (t::cl).
  Proof.
    induction cl.
    - (* BC *)
      simpl.
      case_eq (deduce (fst t) (fst t)) ; try tauto.
      intros.
      generalize (@deduce_prop _ _ _ H env).
      case_eq (unsat t0) ; try tauto.
      { intros.
        generalize (@unsat_prop _ H0 env).
        unfold eval_clause.
        rewrite make_conj_cons.
        simpl; intros.
        tauto.
      }
    - (* IC *)
      simpl.
      case_eq (deduce (fst t) (fst a));
        intros.
      generalize (@deduce_prop _ _ _ H env).
      case_eq (unsat t0); intros.
      {
        generalize (@unsat_prop _ H0 env).
        simpl.
        unfold eval_clause.
        repeat rewrite make_conj_cons.
        tauto.
      }
      destruct (add_term t cl) ; simpl in * ; try tauto.
      {
        intros.
        unfold eval_clause in *.
        repeat rewrite make_conj_cons in *.
        tauto.
      }
      {
        unfold eval_clause in *.
        repeat rewrite make_conj_cons in *.
        tauto.
      }
      destruct (add_term t cl) ; simpl in *;
        unfold eval_clause in * ;
        repeat rewrite make_conj_cons in *; tauto.
  Qed.


  Lemma no_middle_eval_tt : forall env a,
      eval_tt env a \/ ~ eval_tt env a.
  Proof.
    unfold eval_tt.
    auto.
  Qed.

  Hint Resolve no_middle_eval_tt : tauto.

  Lemma or_clause_correct : forall cl cl' env,  eval_opt_clause env (or_clause cl cl') <-> eval_clause env cl \/ eval_clause env cl'.
  Proof.
    induction cl.
    - simpl. unfold eval_clause at 2.  simpl. tauto.
    - intros *.
      simpl.
      assert (HH := add_term_correct env a cl').
      assert (eval_tt env a \/ ~ eval_tt env a) by (apply no_middle_eval').
      destruct (add_term a cl'); simpl in *.
      +
        rewrite IHcl.
        unfold eval_clause in *.
        rewrite !make_conj_cons in *.
        tauto.
      + unfold eval_clause in *.
        repeat rewrite make_conj_cons in *.
        tauto.
  Qed.


  Lemma or_clause_cnf_correct : forall env t f, eval_cnf env (or_clause_cnf t f) <-> (eval_clause env t) \/ (eval_cnf env f).
  Proof.
    unfold eval_cnf.
    unfold or_clause_cnf.
    intros until t.
    set (F := (fun (acc : list clause) (e : clause)  =>
                 match or_clause t e with
                 | Some cl => cl :: acc
                 | None => acc
                 end)).
    intro f.
    assert (  make_conj (eval_clause env) (fold_left F f nil) <-> (eval_clause env t \/ make_conj (eval_clause env) f) /\ make_conj (eval_clause env) nil).
    {
      generalize (@nil clause) as acc.
      induction f.
      - simpl.
        intros ; tauto.
      - intros.
        simpl fold_left.
        rewrite IHf.
        rewrite make_conj_cons.
        unfold F in *; clear F.
        generalize (or_clause_correct t a env).
        destruct (or_clause t a).
        +
          rewrite make_conj_cons.
          simpl. tauto.
        + simpl. tauto.
    }
    destruct t ; auto.
    - unfold eval_clause ; simpl. tauto.
    - unfold xor_clause_cnf.
      unfold F in H.
      rewrite H.
      unfold make_conj at 2. tauto.
  Qed.


  Lemma eval_cnf_cons : forall env a f,  (~ make_conj  (eval_tt env) a  /\ eval_cnf env f) <-> eval_cnf env (a::f).
  Proof.
    intros.
    unfold eval_cnf in *.
    rewrite make_conj_cons ; eauto.
    unfold eval_clause at 2.
    tauto.
  Qed.

  Lemma eval_cnf_cons_iff : forall env a f,  ((~ make_conj  (eval_tt env) a) /\ eval_cnf env f) <-> eval_cnf env (a::f).
  Proof.
    intros.
    unfold eval_cnf in *.
    rewrite make_conj_cons ; eauto.
    unfold eval_clause.
    tauto.
  Qed.


  Lemma or_cnf_correct : forall env f f', eval_cnf env (or_cnf f f') <-> (eval_cnf env  f) \/ (eval_cnf  env f').
  Proof.
    induction f.
    unfold eval_cnf.
    simpl.
    tauto.
    (**)
    intros.
    simpl.
    rewrite eval_cnf_app.
    rewrite <- eval_cnf_cons_iff.
    rewrite IHf.
    rewrite or_clause_cnf_correct.
    unfold eval_clause.
    tauto.
  Qed.

  Lemma or_cnf_opt_correct : forall env f f', eval_cnf env (or_cnf_opt f f') <-> eval_cnf env (or_cnf f f').
  Proof.
    unfold or_cnf_opt.
    intros.
    destruct (is_cnf_tt f) eqn:TF.
    { simpl.
      apply is_cnf_tt_inv in TF.
      subst.
      rewrite or_cnf_correct.
      rewrite eval_cnf_tt.
      tauto.
    }
    destruct (is_cnf_tt f') eqn:TF'.
    { simpl.
      apply is_cnf_tt_inv in TF'.
      subst.
      rewrite or_cnf_correct.
      rewrite eval_cnf_tt.
      tauto.
    }
    { simpl.
      destruct (is_cnf_ff f') eqn:EQ.
      apply is_cnf_ff_inv in EQ.
      subst.
      rewrite or_cnf_correct.
      rewrite eval_cnf_ff.
      tauto.
      tauto.
    }
  Qed.

  Variable eval  : Env -> forall (b:bool), Term -> rtyp b.

  Variable normalise_correct : forall env b t tg, eval_cnf  env (normalise t tg) ->  hold b (eval env b t).

  Variable negate_correct : forall env b t tg, eval_cnf env (negate t tg) -> hold b (eNOT b (eval env b t)).

  Definition e_rtyp (b : bool) (x : rtyp b) : rtyp b := x.

  Lemma hold_eTT : forall b, hold b (eTT b).
  Proof.
    destruct b ; simpl; auto.
  Qed.

  Hint Resolve hold_eTT : tauto.

  Lemma hold_eFF : forall b,
      hold b (eNOT b (eFF b)).
  Proof.
    destruct b ; simpl;auto.
  Qed.

  Hint Resolve hold_eFF : tauto.

  Lemma hold_eAND : forall b r1 r2,
      hold b (eAND b r1 r2) <-> (hold b r1 /\ hold b r2).
  Proof.
    destruct b ; simpl.
    - intros. apply iff_refl.
    - apply andb_true_iff.
  Qed.

  Lemma hold_eOR : forall b r1 r2,
      hold b (eOR b r1 r2) <-> (hold b r1 \/ hold b r2).
  Proof.
    destruct b ; simpl.
    - intros. apply iff_refl.
    - apply orb_true_iff.
  Qed.

  Lemma hold_eNOT : forall b e,
      hold b (eNOT b e) <-> not (hold b e).
  Proof.
    destruct b ; simpl.
    - intros. apply iff_refl.
    - intros. unfold is_true.
      rewrite negb_true_iff.
      destruct e ; intuition congruence.
  Qed.

  Lemma hold_eIMPL : forall b e1 e2,
      hold b (eIMPL b e1 e2) <-> (hold b e1 -> hold b e2).
  Proof.
    destruct b ; simpl.
    - intros. apply iff_refl.
    - intros.
      unfold is_true.
      destruct e1,e2 ; simpl ; intuition congruence.
  Qed.

  Lemma hold_eIFF : forall b e1 e2,
      hold b (eIFF b e1 e2) <-> (hold b e1 <-> hold b e2).
  Proof.
    destruct b ; simpl.
    - intros. apply iff_refl.
    - intros.
      unfold is_true.
      rewrite eqb_true_iff.
      destruct e1,e2 ; simpl ; intuition congruence.
  Qed.



  Lemma xcnf_impl :
    forall
      (b : bool)
      (f1 : GFormula b)
      (o : option unit)
      (f2 : GFormula b)
      (IHf1 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f1) ->
          hold b (eval_f e_rtyp (eval env) (if pol then f1 else NOT f1)))
      (IHf2 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f2) ->
          hold b (eval_f e_rtyp (eval env) (if pol then f2 else NOT f2))),
    forall (pol : bool) (env : Env),
      eval_cnf env (xcnf pol (IMPL f1 o f2)) ->
      hold b (eval_f e_rtyp (eval env) (if pol then IMPL f1 o f2 else NOT (IMPL f1 o f2))).
  Proof.
    simpl; intros. unfold mk_impl in H.
    destruct pol.
    + simpl.
      rewrite hold_eIMPL.
      intro.
      rewrite or_cnf_opt_correct in H.
      rewrite or_cnf_correct in H.
      destruct H as [H | H].
      generalize (IHf1 _ _ H).
      simpl in *.
      rewrite hold_eNOT.
      tauto.
      generalize (IHf2 _ _ H).
      auto.
    + (* pol = false *)
      rewrite eval_cnf_and_opt in H.
      unfold and_cnf in H.
      simpl in H.
      rewrite eval_cnf_app in H.
      destruct H as [H0 H1].
      generalize (IHf1 _ _ H0).
      generalize (IHf2 _ _ H1).
      simpl.
      rewrite ! hold_eNOT.
      rewrite ! hold_eIMPL.
      tauto.
  Qed.

  Lemma hold_eIFF_IMPL : forall b e1 e2,
      hold b (eIFF b e1 e2) <-> (hold b (eAND b (eIMPL b e1 e2) (eIMPL b e2 e1))).
  Proof.
    intros.
    rewrite hold_eIFF.
    rewrite hold_eAND.
    rewrite! hold_eIMPL.
    tauto.
  Qed.

  Lemma hold_eEQ : forall e1 e2,
      hold false (eIFF false e1 e2) <-> e1 = e2.
  Proof.
    simpl.
    destruct e1,e2 ; simpl ; intuition congruence.
  Qed.


  Lemma xcnf_iff : forall
      (b : bool)
      (f1 f2 : @GFormula Term rtyp Annot unit b)
      (IHf1 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f1) ->
          hold b (eval_f e_rtyp (eval env) (if pol then f1 else NOT f1)))
      (IHf2 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f2) ->
          hold b (eval_f e_rtyp (eval env) (if pol then f2 else NOT f2))),
      forall (pol : bool) (env : Env),
        eval_cnf env (xcnf pol (IFF f1 f2)) ->
        hold b (eval_f e_rtyp (eval env) (if pol then IFF f1 f2 else NOT (IFF f1 f2))).
  Proof.
    simpl.
    intros.
    rewrite mk_iff_is_bool in H.
    unfold mk_iff in H.
    destruct pol;
      rewrite or_cnf_opt_correct in H;
      rewrite or_cnf_correct in H;
      rewrite! eval_cnf_and_opt in H;
      unfold and_cnf in H;
      rewrite! eval_cnf_app in H;
      generalize (IHf1 false env);
      generalize (IHf1 true env);
      generalize (IHf2 false env);
      generalize (IHf2 true env);
      simpl.
    -
      rewrite hold_eIFF_IMPL.
      rewrite hold_eAND.
      rewrite! hold_eIMPL.
      rewrite! hold_eNOT.
      tauto.
    -  rewrite! hold_eNOT.
       rewrite hold_eIFF_IMPL.
       rewrite hold_eAND.
       rewrite! hold_eIMPL.
       tauto.
  Qed.

  Lemma xcnf_correct : forall (b:bool) (f : @GFormula Term rtyp Annot unit b)  pol env,
      eval_cnf env (xcnf pol f) -> hold b (eval_f e_rtyp (eval env) (if pol then f else NOT f)).
  Proof.
    induction f.
    - (* TT *)
      unfold eval_cnf.
      simpl.
      destruct pol ; intros; simpl; auto with tauto.
      rewrite eval_cnf_ff in H. tauto.
    - (* FF *)
      destruct pol ; simpl in *; intros; auto with tauto.
      + rewrite eval_cnf_ff in H. tauto.
    - (* P *)
      simpl.
      destruct pol ; intros ;simpl.
      + rewrite eval_cnf_ff in H. tauto.
      + rewrite eval_cnf_ff in H. tauto.
    - (* A *)
      simpl.
      destruct pol ; simpl.
      intros.
      eapply normalise_correct  ; eauto.
      (* A 2 *)
      intros.
      eapply  negate_correct ; eauto.
    - (* AND *)
      destruct pol ; simpl.
      + (* pol = true *)
        intros.
        rewrite eval_cnf_and_opt in H.
        unfold and_cnf in H.
        rewrite eval_cnf_app  in H.
        destruct H.
        apply hold_eAND; split.
        apply (IHf1 _ _ H).
        apply (IHf2 _ _ H0).
      +  (* pol = false *)
        intros.
        apply hold_eNOT.
        rewrite hold_eAND.
        rewrite or_cnf_opt_correct in H.
        rewrite or_cnf_correct in H.
        destruct H as [H | H].
        generalize (IHf1 false  env H).
        simpl.
        rewrite hold_eNOT.
        tauto.
        generalize (IHf2 false  env H).
        simpl.
        rewrite hold_eNOT.
        tauto.
    - (* OR *)
      simpl.
      destruct pol.
      + (* pol = true *)
        intros. unfold mk_or in H.
        rewrite or_cnf_opt_correct in H.
        rewrite or_cnf_correct in H.
        destruct H as [H | H].
        generalize (IHf1 _  env H).
        simpl.
        rewrite hold_eOR.
        tauto.
        generalize (IHf2 _  env H).
        simpl.
        rewrite hold_eOR.
        tauto.
      + (* pol = true *)
        intros. unfold mk_or in H.
        rewrite eval_cnf_and_opt in H.
        unfold and_cnf.
        rewrite eval_cnf_app in H.
        destruct H as [H0 H1].
        simpl.
        generalize (IHf1 _ _ H0).
        generalize (IHf2 _ _ H1).
        simpl.
        rewrite ! hold_eNOT.
        rewrite ! hold_eOR.
        tauto.
    - (**)
      simpl.
      destruct pol ; simpl.
      intros.
      apply (IHf false) ; auto.
      intros.
      generalize (IHf _ _ H).
      rewrite ! hold_eNOT.
      tauto.
    - (* IMPL *)
      apply xcnf_impl; auto.
    - apply xcnf_iff ; auto.
    - simpl.
      destruct (is_bool f2) eqn:EQ.
      + apply is_bool_inv in EQ.
        destruct b; subst; intros;
          apply IHf1 in H;
          destruct pol ; simpl in * ; auto.
        * unfold is_true in H.
          rewrite negb_true_iff in H.
          congruence.
        *
          unfold is_true in H.
          rewrite negb_true_iff in H.
          congruence.
        * unfold is_true in H.
          congruence.
      + intros.
        rewrite <- mk_iff_is_bool in H.
        apply xcnf_iff in H; auto.
        simpl in H.
        destruct pol ; simpl in *.
        rewrite <- hold_eEQ.
        simpl; auto.
        rewrite <- hold_eEQ.
        simpl; auto.
        unfold is_true in *.
        rewrite negb_true_iff in H.
        congruence.
  Qed.

  Variable Witness : Type.
  Variable checker : list (Term'*Annot) -> Witness -> bool.

  Variable checker_sound : forall t  w, checker t w = true -> forall env, make_impl (eval_tt env)  t False.

  Fixpoint cnf_checker (f : cnf) (l : list Witness)  {struct f}: bool :=
    match f with
    | nil => true
    | e::f => match l with
              | nil => false
              | c::l => match checker e c with
                        | true => cnf_checker f l
                        |   _  => false
                        end
              end
    end.

  Lemma cnf_checker_sound : forall t  w, cnf_checker t w = true -> forall env, eval_cnf  env  t.
  Proof.
    unfold eval_cnf.
    induction t.
    (* bc *)
    simpl.
    auto.
    (* ic *)
    simpl.
    destruct w.
    intros ; discriminate.
    case_eq (checker a w) ; intros ; try discriminate.
    generalize (@checker_sound _ _ H env).
    generalize (IHt _ H0 env) ; intros.
    destruct t.
    red ; intro.
    rewrite <- make_conj_impl in H2.
    tauto.
    rewrite <- make_conj_impl in H2.
    tauto.
  Qed.

  Definition tauto_checker (f:@GFormula Term rtyp Annot unit true) (w:list Witness) : bool :=
    cnf_checker (xcnf true f) w.

  Lemma tauto_checker_sound : forall t  w, tauto_checker t w = true -> forall env, eval_f e_rtyp (eval env)  t.
  Proof.
    unfold tauto_checker.
    intros.
    change (eval_f e_rtyp (eval env) t) with (eval_f e_rtyp (eval env) (if true then t else TT true)).
    apply (xcnf_correct t true).
    eapply cnf_checker_sound ; eauto.
  Qed.

  Definition eval_bf {A : Type} (ea : forall (b:bool), A -> rtyp b) (b:bool) (f: BFormula A b) := eval_f e_rtyp ea f.

  Lemma eval_bf_map : forall T U (fct: T-> U) env (b:bool) (f:BFormula T b) ,
      eval_bf env  (map_bformula fct f)  = eval_bf (fun b x => env b (fct x)) f.
  Proof.
    induction f ; simpl ; try (rewrite IHf1 ; rewrite IHf2) ; auto.
    rewrite <- IHf.  auto.
  Qed.


End S.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
