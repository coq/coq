(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Set Implicit Arguments.


Section S.
  Context {TA  : Type}. (* type of interpreted atoms *)
  Context {TX  : Type}. (* type of uninterpreted terms (Prop) *)
  Context {AA  : Type}. (* type of annotations for atoms *)
  Context {AF  : Type}. (* type of formulae identifiers *)

   Inductive GFormula  : Type :=
  | TT   : GFormula
  | FF   : GFormula
  | X    : TX -> GFormula
  | A    : TA -> AA -> GFormula
  | Cj   : GFormula  -> GFormula  -> GFormula
  | D    : GFormula  -> GFormula  -> GFormula
  | N    : GFormula  -> GFormula
  | I    : GFormula  -> option AF -> GFormula  -> GFormula.

  Section MAPX.
    Variable F : TX -> TX.

    Fixpoint mapX (f : GFormula) : GFormula :=
      match f with
      | TT => TT
      | FF => FF
      | X x => X (F x)
      | A a an => A a an
      | Cj f1 f2 => Cj (mapX f1) (mapX f2)
      | D f1 f2  => D (mapX f1) (mapX f2)
      | N f      => N (mapX f)
      | I f1 o f2 => I (mapX f1) o (mapX f2)
      end.

  End MAPX.

  Section FOLDANNOT.
    Variable ACC : Type.
    Variable F : ACC -> AA -> ACC.

    Fixpoint foldA (f : GFormula) (acc : ACC) : ACC :=
      match f with
      | TT => acc
      | FF => acc
      | X x => acc
      | A a an => F acc an
      | Cj f1 f2
      | D f1 f2
      | I f1 _ f2 => foldA f1 (foldA f2 acc)
      | N f      => foldA f acc
      end.

  End FOLDANNOT.


  Definition cons_id (id : option AF) (l : list AF) :=
    match id with
    | None => l
    | Some id => id :: l
    end.

  Fixpoint ids_of_formula f :=
    match f with
    | I f id f' => cons_id id (ids_of_formula f')
    |  _           => nil
    end.

  Fixpoint collect_annot (f : GFormula) : list AA :=
    match f with
    | TT | FF | X _ => nil
    | A _ a => a ::nil
    | Cj f1 f2
    | D  f1 f2
    | I f1 _ f2  => collect_annot f1 ++ collect_annot f2
    | N  f       => collect_annot f
    end.

  Variable ex : TX -> Prop. (* [ex] will be the identity *)

  Section EVAL.

  Variable ea : TA -> Prop.

  Fixpoint eval_f (f:GFormula) {struct f}: Prop :=
  match f with
  | TT  => True
  | FF  => False
  | A a _ =>  ea a
  | X  p => ex p
  | Cj e1 e2 => (eval_f e1) /\ (eval_f e2)
  | D e1 e2  => (eval_f e1) \/ (eval_f e2)
  | N e     => ~ (eval_f e)
  | I f1 _ f2 => (eval_f f1) -> (eval_f f2)
  end.


  End EVAL.





  Lemma eval_f_morph :
    forall  (ev ev' : TA -> Prop) (f : GFormula),
      (forall a, ev a <-> ev' a) -> (eval_f ev f <-> eval_f ev' f).
  Proof.
    induction f ; simpl ; try tauto.
    intros.
    apply H.
  Qed.


End S.



(** Typical boolean formulae *)
Definition BFormula (A : Type) := @GFormula A Prop unit unit.

Section MAPATOMS.
  Context {TA TA':Type}.
  Context {TX  : Type}.
  Context {AA  : Type}.
  Context {AF  : Type}.


Fixpoint map_bformula (fct : TA -> TA') (f : @GFormula TA TX AA AF ) : @GFormula TA' TX AA AF :=
  match f with
  | TT  => TT
  | FF  => FF
  | X p => X  p
  | A a t => A (fct a) t
  | Cj f1 f2 => Cj (map_bformula fct f1) (map_bformula fct f2)
  | D f1 f2 => D (map_bformula fct f1) (map_bformula fct f2)
  | N f     => N (map_bformula fct f)
  | I f1 a f2 => I (map_bformula fct f1) a (map_bformula fct f2)
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
      AF i s unit in Coq and Names.Id.t in Ocaml
     *)
    Definition TFormula (TX: Type) (AF: Type) := @GFormula Term TX Annot AF.


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
      else and_cnf f1 f2.

    Definition or_cnf_opt (f1 : cnf) (f2 : cnf) : cnf :=
      if is_cnf_tt f1 || is_cnf_tt f2
      then cnf_tt
      else if is_cnf_ff f2
           then f1 else or_cnf f1 f2.

    Fixpoint xcnf {TX AF: Type} (pol : bool) (f : TFormula TX AF)  {struct f}: cnf :=
      match f with
      | TT  => if pol then cnf_tt else cnf_ff
      | FF  => if pol then cnf_ff else cnf_tt
      | X  p => if pol then cnf_ff else cnf_ff (* This is not complete - cannot negate any proposition *)
      | A x t => if pol then normalise x  t else negate x  t
      | N e  => xcnf (negb pol) e
      | Cj e1 e2 =>
        (if pol then and_cnf_opt else or_cnf_opt) (xcnf pol e1) (xcnf pol e2)
      | D e1 e2  => (if pol then or_cnf_opt else and_cnf_opt) (xcnf pol e1) (xcnf pol e2)
      | I e1 _ e2
        =>  (if pol then or_cnf_opt else and_cnf_opt) (xcnf (negb pol) e1) (xcnf pol e2)
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

      Fixpoint rxcnf {TX AF: Type}(polarity : bool) (f : TFormula TX AF) : cnf * list Annot :=
        match f with
        | TT => if polarity then (cnf_tt,nil) else (cnf_ff,nil)
        | FF  => if polarity then (cnf_ff,nil) else (cnf_tt,nil)
        | X p => if polarity then (cnf_ff,nil) else (cnf_ff,nil)
        | A x t  => ratom (if polarity then normalise x t else negate x t) t
        | N e  => rxcnf (negb polarity) e
        | Cj e1 e2 =>
          let '(e1,t1) := rxcnf polarity e1 in
          let '(e2,t2) := rxcnf polarity e2 in
          if polarity
          then  (and_cnf_opt e1  e2, t1 +++ t2)
          else let (f',t') := ror_cnf_opt e1 e2 in
            (f', t1 +++ t2 +++ t')
        | D e1 e2  =>
          let '(e1,t1) := rxcnf polarity e1 in
          let '(e2,t2) := rxcnf polarity e2 in
          if polarity
       then let (f',t') := ror_cnf_opt e1 e2 in
            (f', t1 +++ t2 +++ t')
          else (and_cnf_opt e1 e2, t1 +++ t2)
        | I e1 a e2 =>
          let '(e1 , t1) := (rxcnf (negb polarity) e1) in
          if polarity
          then
            if is_cnf_ff e1
            then
              rxcnf polarity e2
            else (* compute disjunction *)
              let '(e2 , t2) := (rxcnf polarity e2) in
              let (f',t') := ror_cnf_opt e1 e2 in
              (f', t1 +++ t2 +++ t') (* record the hypothesis *)
          else
            let '(e2 , t2) := (rxcnf polarity e2) in
            (and_cnf_opt e1 e2, t1 +++ t2)
        end.


      Section Abstraction.
        Variable TX : Type.
        Variable AF : Type.

        Class to_constrT : Type :=
          {
            mkTT : TX;
            mkFF : TX;
            mkA  : Term -> Annot -> TX;
            mkCj : TX -> TX -> TX;
            mkD  : TX -> TX -> TX;
            mkI  : TX -> TX -> TX;
            mkN  : TX -> TX
          }.

        Context {to_constr : to_constrT}.

        Fixpoint aformula (f : TFormula TX AF) : TX :=
          match f with
          | TT => mkTT
          | FF => mkFF
          | X p => p
          | A x t => mkA x t
          | Cj f1 f2 => mkCj (aformula f1) (aformula f2)
          | D  f1 f2 => mkD (aformula f1) (aformula f2)
          | I f1 o f2 => mkI (aformula f1) (aformula f2)
          | N f       => mkN (aformula f)
          end.


        Definition is_X (f : TFormula TX AF) : option TX :=
          match f with
          | X p => Some p
          | _   => None
          end.

        Definition is_X_inv : forall f x,
            is_X f = Some x -> f = X x.
        Proof.
          destruct f ; simpl ; congruence.
        Qed.


        Variable needA : Annot -> bool.

        Definition abs_and (f1 f2 : TFormula TX AF)
                   (c : TFormula TX AF -> TFormula TX AF -> TFormula TX AF) :=
          match is_X f1 , is_X f2 with
          | Some _  , _ | _ , Some _ => X (aformula (c f1  f2))
          |   _     , _ => c f1 f2
          end.

        Definition abs_or (f1 f2 : TFormula TX AF)
                   (c : TFormula TX AF -> TFormula TX AF -> TFormula TX AF) :=
          match is_X f1 , is_X f2 with
          | Some _  , Some _ => X (aformula (c f1  f2))
          |   _     , _ => c f1 f2
          end.

        Definition mk_arrow (o : option AF) (f1 f2: TFormula TX AF) :=
          match o with
          | None => I f1 None f2
          | Some _ => if is_X f1 then f2 else I f1 o f2
          end.


        Fixpoint abst_form  (pol : bool) (f : TFormula TX AF) :=
          match f with
          | TT => if pol then TT else X mkTT
          | FF => if pol then X mkFF else FF
          | X p => X p
          | A x t => if needA t then A x t else X (mkA x t)
          | Cj f1 f2 =>
            let f1 := abst_form pol f1 in
            let f2 := abst_form pol f2 in
            if pol then abs_and f1 f2 Cj
            else abs_or f1 f2 Cj
          | D f1 f2 =>
            let f1 := abst_form pol f1 in
            let f2 := abst_form pol f2 in
            if pol then abs_or f1 f2 D
            else abs_and f1 f2 D
          | I f1 o f2 =>
            let f1 := abst_form (negb pol) f1 in
            let f2 := abst_form pol f2 in
            if pol
            then abs_or f1 f2 (mk_arrow o)
            else abs_and f1 f2 (mk_arrow o)
          | N f => let f := abst_form (negb pol) f in
                   match is_X f with
                   | Some a => X (mkN a)
                   |  _     => N f
                   end
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

      Lemma abs_and_pol : forall f1 f2 pol,
          and_cnf_opt (xcnf pol f1) (xcnf pol f2) =
          xcnf pol (abs_and f1 f2 (if pol then Cj else D)).
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

      Lemma abs_or_pol : forall f1 f2 pol,
          or_cnf_opt (xcnf pol f1) (xcnf pol f2) =
          xcnf pol (abs_or f1 f2 (if pol then D else Cj)).
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

      Lemma xcnf_true_mk_arrow_l : forall o t f,
        xcnf true (mk_arrow o (X t) f) = xcnf true f.
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

      Lemma xcnf_true_mk_arrow_r : forall o t f,
          xcnf true (mk_arrow o  f (X t)) = xcnf false f.
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



      Lemma abst_form_correct : forall f pol,
          xcnf pol f = xcnf pol (abst_form pol f).
      Proof.
        induction f;intros.
        - simpl. destruct pol ; reflexivity.
        - simpl. destruct pol ; reflexivity.
        - simpl. reflexivity.
        - simpl. rewrite needA_all.
          reflexivity.
        - simpl.
          specialize (IHf1 pol).
          specialize (IHf2 pol).
          rewrite IHf1.
          rewrite IHf2.
          destruct pol.
          +
            apply abs_and_pol; auto.
          +
            apply abs_or_pol; auto.
        - simpl.
          specialize (IHf1 pol).
          specialize (IHf2 pol).
          rewrite IHf1.
          rewrite IHf2.
          destruct pol.
          +
            apply abs_or_pol; auto.
          +
            apply abs_and_pol; auto.
        -  simpl.
           specialize (IHf (negb pol)).
           destruct (is_X (abst_form (negb pol) f)) eqn:EQ1.
           + apply is_X_inv in EQ1.
             rewrite EQ1 in *.
             simpl in *.
             destruct pol ; auto.
           + simpl. congruence.
        - simpl.
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



      Lemma rxcnf_xcnf : forall {TX AF:Type} (f:TFormula TX AF) b,
        fst (rxcnf  b f) = xcnf b f.
      Proof.
        induction f ; simpl ; auto.
        - destruct b; simpl ; auto.
        - destruct b; simpl ; auto.
        - destruct b ; simpl ; auto.
        - intros. rewrite ratom_cnf. reflexivity.
        - intros.
          specialize (IHf1 b).
          specialize (IHf2 b).
          destruct (rxcnf b f1).
          destruct (rxcnf b f2).
          simpl in *.
          subst. destruct b ; auto.
          rewrite <- ror_opt_cnf_cnf.
          destruct (ror_cnf_opt (xcnf false f1) (xcnf false f2)).
          reflexivity.
        - intros.
          specialize (IHf1 b).
          specialize (IHf2 b).
          rewrite <- IHf1.
          rewrite <- IHf2.
          destruct (rxcnf b f1).
          destruct (rxcnf b f2).
          simpl in *.
          subst. destruct b ; auto.
          rewrite <- ror_opt_cnf_cnf.
          destruct (ror_cnf_opt (xcnf true f1) (xcnf true f2)).
          reflexivity.
        - intros.
          specialize (IHf1 (negb b)).
          specialize (IHf2 b).
          rewrite <- IHf1.
          rewrite <- IHf2.
          destruct (rxcnf (negb b) f1).
          destruct (rxcnf b f2).
          simpl in *.
          subst.
          destruct b;auto.
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


    Variable eval  : Env -> Term -> Prop.

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




  Variable normalise_correct : forall env t tg, eval_cnf  env (normalise t tg) -> eval env t.

  Variable negate_correct : forall env t tg, eval_cnf env (negate t tg) -> ~ eval env t.

  Lemma xcnf_correct : forall (f : @GFormula Term Prop Annot unit)  pol env, eval_cnf env (xcnf pol f) -> eval_f (fun x => x) (eval env) (if pol then f else N f).
  Proof.
    induction f.
    - (* TT *)
    unfold eval_cnf.
    simpl.
    destruct pol ; simpl ; auto.
    - (* FF *)
    unfold eval_cnf.
    destruct pol; simpl ; auto.
    unfold eval_clause ; simpl.
    tauto.
    - (* P *)
    simpl.
    destruct pol ; intros ;simpl.
    unfold eval_cnf in H.
    (* Here I have to drop the proposition *)
    simpl in H.
    unfold eval_clause in H ; simpl in H.
    tauto.
    (* Here, I could store P in the clause *)
    unfold eval_cnf in H;simpl in H.
    unfold eval_clause in H ; simpl in H.
    tauto.
    - (* A *)
    simpl.
    destruct pol ; simpl.
    intros.
    eapply normalise_correct  ; eauto.
    (* A 2 *)
    intros.
    eapply  negate_correct ; eauto.
    - (* Cj *)
    destruct pol ; simpl.
    + (* pol = true *)
    intros.
    rewrite eval_cnf_and_opt in H.
    unfold and_cnf in H.
    rewrite eval_cnf_app  in H.
    destruct H.
    split.
    apply (IHf1 _ _ H).
    apply (IHf2 _ _ H0).
    +  (* pol = false *)
    intros.
    rewrite or_cnf_opt_correct in H.
    rewrite or_cnf_correct in H.
    destruct H as [H | H].
    generalize (IHf1 false  env H).
    simpl.
    tauto.
    generalize (IHf2 false  env H).
    simpl.
    tauto.
    - (* D *)
    simpl.
    destruct pol.
    + (* pol = true *)
    intros.
    rewrite or_cnf_opt_correct in H.
    rewrite or_cnf_correct in H.
    destruct H as [H | H].
    generalize (IHf1 _  env H).
    simpl.
    tauto.
    generalize (IHf2 _  env H).
    simpl.
    tauto.
    + (* pol = true *)
    intros.
    rewrite eval_cnf_and_opt in H.
    unfold and_cnf.
    rewrite eval_cnf_app in H.
    destruct H as [H0 H1].
    simpl.
    generalize (IHf1 _ _ H0).
    generalize (IHf2 _ _ H1).
    simpl.
    tauto.
    - (**)
    simpl.
    destruct pol ; simpl.
    intros.
    apply (IHf false) ; auto.
    intros.
    generalize (IHf _ _ H).
    tauto.
    - (* I *)
    simpl; intros.
    destruct pol.
    + simpl.
    intro.
    rewrite or_cnf_opt_correct in H.
    rewrite or_cnf_correct in H.
    destruct H as [H | H].
    generalize (IHf1 _ _ H).
    simpl in *.
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
      tauto.
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


  Definition tauto_checker (f:@GFormula Term Prop Annot unit) (w:list Witness) : bool :=
    cnf_checker (xcnf true f) w.

  Lemma tauto_checker_sound : forall t  w, tauto_checker t w = true -> forall env, eval_f (fun x => x) (eval env)  t.
  Proof.
    unfold tauto_checker.
    intros.
    change (eval_f (fun x => x) (eval env) t) with (eval_f (fun x => x) (eval env) (if true then t else TT)).
    apply (xcnf_correct t true).
    eapply cnf_checker_sound ; eauto.
  Qed.

  Definition eval_bf {A : Type} (ea : A -> Prop) (f: BFormula A) := eval_f (fun x => x) ea f.


  Lemma eval_bf_map : forall T U (fct: T-> U) env f ,
    eval_bf env  (map_bformula fct f)  = eval_bf (fun x => env (fct x)) f.
Proof.
  induction f ; simpl ; try (rewrite IHf1 ; rewrite IHf2) ; auto.
  rewrite <- IHf.  auto.
Qed.


End S.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
