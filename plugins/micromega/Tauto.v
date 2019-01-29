(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

    (*    Definition or_clause_cnf (t:clause) (f:cnf) : cnf :=
          List.map (fun x => (t++x)) f. *)

    Definition or_clause_cnf (t:clause) (f:cnf) : cnf :=
      List.fold_right (fun e acc =>
                         match or_clause t e with
                         | None => acc
                         | Some cl => cl :: acc
                         end) nil f.


    Fixpoint or_cnf (f : cnf) (f' : cnf) {struct f}: cnf :=
      match f with
      | nil => cnf_tt
      | e :: rst => (or_cnf rst f') ++ (or_clause_cnf e f')
      end.


    Definition and_cnf (f1 : cnf) (f2 : cnf) : cnf :=
      f1 ++ f2.

    (** TX is Prop in Coq and EConstr.constr in Ocaml.
      AF i s unit in Coq and Names.Id.t in Ocaml
     *)
    Definition TFormula (TX: Type) (AF: Type) := @GFormula Term TX Annot AF.

    Fixpoint xcnf {TX AF: Type} (pol : bool) (f : TFormula TX AF)  {struct f}: cnf :=
      match f with
      | TT  => if pol then cnf_tt else cnf_ff
      | FF  => if pol then cnf_ff else cnf_tt
      | X  p => if pol then cnf_ff else cnf_ff (* This is not complete - cannot negate any proposition *)
      | A x t => if pol then normalise x  t else negate x  t
      | N e  => xcnf (negb pol) e
      | Cj e1 e2 =>
        (if pol then and_cnf else or_cnf) (xcnf pol e1) (xcnf pol e2)
      | D e1 e2  => (if pol then or_cnf else and_cnf) (xcnf pol e1) (xcnf pol e2)
      | I e1 _ e2 => (if pol then or_cnf else and_cnf) (xcnf (negb pol) e1) (xcnf pol e2)
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

      Definition ror_clause_cnf t f :=
        List.fold_right (fun e '(acc,tg) =>
                           match ror_clause t e with
                           | inl cl => (cl :: acc,tg)
                           | inr l => (acc,tg++l)
                           end) (nil,nil) f .


      Fixpoint ror_cnf f f' :=
        match f with
        | nil => (cnf_tt,nil)
        | e :: rst =>
          let (rst_f',t) := ror_cnf rst f' in
          let (e_f', t') := ror_clause_cnf e f' in
          (rst_f' ++ e_f', t ++ t')
        end.

      Fixpoint rxcnf {TX AF: Type}(polarity : bool) (f : TFormula TX AF) :=
        match f with
        | TT => if polarity then (cnf_tt,nil) else (cnf_ff,nil)
        | FF  => if polarity then (cnf_ff,nil) else (cnf_tt,nil)
        | X p => if polarity then (cnf_ff,nil) else (cnf_ff,nil)
        | A x t  => ((if polarity then normalise x t else negate x t),nil)
        | N e  => rxcnf (negb polarity) e
        | Cj e1 e2 =>
          let (e1,t1) := rxcnf polarity e1 in
          let (e2,t2) := rxcnf polarity e2 in
          if polarity
          then  (e1 ++ e2, t1 ++ t2)
       else let (f',t') := ror_cnf e1 e2 in
            (f', t1 ++ t2 ++ t')
        | D e1 e2  =>
          let (e1,t1) := rxcnf polarity e1 in
          let (e2,t2) := rxcnf polarity e2 in
          if polarity
       then let (f',t') := ror_cnf e1 e2 in
            (f', t1 ++ t2 ++ t')
          else (e1 ++ e2, t1 ++ t2)
        | I e1 _ e2 =>
          let (e1 , t1) := (rxcnf (negb polarity) e1) in
          let (e2 , t2) := (rxcnf polarity e2) in
          if polarity
          then let (f',t') := ror_cnf e1 e2 in
               (f', t1 ++ t2 ++ t')
          else (and_cnf e1 e2, t1 ++ t2)
        end.

      End CNFAnnot.



    Variable eval  : Env -> Term -> Prop.

    Variable eval'  : Env -> Term' -> Prop.

    Variable no_middle_eval' : forall env d, (eval' env d) \/ ~ (eval' env d).


    Variable unsat_prop : forall t, unsat t  = true ->
                                    forall env, eval' env t -> False.



    Variable deduce_prop : forall env t t' u,
        eval' env t -> eval' env t' -> deduce t t' = Some u -> eval' env u.



    Definition eval_tt (env : Env) (tt : Term' * Annot) := eval' env (fst tt).


    Definition eval_clause (env : Env) (cl : clause) := ~ make_conj  (eval_tt env) cl.

    Definition eval_cnf (env : Env) (f:cnf) := make_conj  (eval_clause  env) f.


    Lemma eval_cnf_app : forall env x y, eval_cnf env (x++y) -> eval_cnf env x /\ eval_cnf env y.
    Proof.
      unfold eval_cnf.
      intros.
      rewrite make_conj_app in H ; auto.
    Qed.


    Definition eval_opt_clause (env : Env) (cl: option clause) :=
      match cl with
      | None => True
      | Some cl => eval_clause env cl
      end.


  Lemma add_term_correct : forall env t cl , eval_opt_clause env (add_term t cl) -> eval_clause env (t::cl).
  Proof.
    induction cl.
    - (* BC *)
    simpl.
    case_eq (deduce (fst t) (fst t)) ; auto.
    intros *.
    case_eq (unsat t0) ; auto.
    unfold eval_clause.
    rewrite make_conj_cons.
    intros. intro.
    apply unsat_prop with (1:= H) (env := env).
    apply deduce_prop with (3:= H0) ; tauto.
    - (* IC *)
    simpl.
    case_eq (deduce (fst t) (fst a)).
    intro u.
    case_eq (unsat u).
    simpl. intros.
    unfold eval_clause.
    intro.
    apply unsat_prop  with (1:= H) (env:= env).
    repeat rewrite make_conj_cons in H2.
    apply deduce_prop with (3:= H0); tauto.
    intro.
    case_eq (add_term t cl) ; intros.
    simpl in H2.
    rewrite H0 in IHcl.
    simpl in IHcl.
    unfold eval_clause in *.
    intros.
    repeat rewrite make_conj_cons in *.
    tauto.
    rewrite H0 in IHcl ; simpl in *.
    unfold eval_clause in *.
    intros.
    repeat rewrite make_conj_cons in *.
    tauto.
    case_eq (add_term t cl) ; intros.
    simpl in H1.
    unfold eval_clause in *.
    repeat rewrite make_conj_cons in *.
    rewrite H in IHcl.
    simpl in IHcl.
    tauto.
    simpl in *.
    rewrite H in IHcl.
    simpl in IHcl.
    unfold eval_clause in *.
    repeat rewrite make_conj_cons in *.
    tauto.
  Qed.


  Lemma no_middle_eval_tt : forall env a,
      eval_tt env a \/ ~ eval_tt env a.
  Proof.
    unfold eval_tt.
    auto.
  Qed.

  Hint Resolve no_middle_eval_tt : tauto.

  Lemma or_clause_correct : forall cl cl' env,  eval_opt_clause env (or_clause cl cl') -> eval_clause env cl \/ eval_clause env cl'.
  Proof.
    induction cl.
    - simpl. tauto.
    - intros *.
      simpl.
      assert (HH := add_term_correct env a cl').
      case_eq (add_term a cl').
      +
      intros.
      apply IHcl in H0.
      rewrite H in HH.
      simpl in HH.
      unfold eval_clause in *.
      destruct H0.
      *
      repeat rewrite make_conj_cons in *.
      tauto.
      * apply HH in H0.
        apply not_make_conj_cons in H0 ; auto with tauto.
        repeat rewrite make_conj_cons in *.
        tauto.
      +
      intros.
      rewrite H in HH.
      simpl in HH.
      unfold eval_clause in *.
      assert (HH' := HH Coq.Init.Logic.I).
      apply not_make_conj_cons in HH'; auto with tauto.
      repeat rewrite make_conj_cons in *.
      tauto.
  Qed.


  Lemma or_clause_cnf_correct : forall env t f, eval_cnf env (or_clause_cnf t f) -> (eval_clause env t) \/ (eval_cnf env f).
  Proof.
    unfold eval_cnf.
    unfold or_clause_cnf.
    intros until t.
    set (F := (fun (e : clause) (acc : list clause) =>
                 match or_clause t e with
                 | Some cl => cl :: acc
                 | None => acc
                 end)).
    induction f;auto.
    simpl.
    intros.
    destruct f.
    -  simpl in H.
       simpl in IHf.
       unfold F in H.
       revert H.
       intros.
       apply or_clause_correct.
       destruct (or_clause t a) ; simpl in * ; auto.
    -
      unfold F in H at 1.
      revert H.
      assert (HH := or_clause_correct t a env).
      destruct (or_clause t a); simpl in HH ;
        rewrite make_conj_cons in * ; intuition.
      rewrite make_conj_cons in *.
      tauto.
  Qed.


  Lemma eval_cnf_cons : forall env a f,  (~ make_conj  (eval_tt env) a) -> eval_cnf env f -> eval_cnf env (a::f).
  Proof.
    intros.
    unfold eval_cnf in *.
    rewrite make_conj_cons ; eauto.
  Qed.

  Lemma or_cnf_correct : forall env f f', eval_cnf env (or_cnf f f') -> (eval_cnf env  f) \/ (eval_cnf  env f').
  Proof.
    induction f.
    unfold eval_cnf.
    simpl.
    tauto.
    (**)
    intros.
    simpl in H.
    destruct (eval_cnf_app _ _ _ H).
    clear H.
    destruct (IHf _ H0).
    destruct (or_clause_cnf_correct _ _ _ H1).
    left.
    apply eval_cnf_cons ; auto.
    right ; auto.
    right ; auto.
  Qed.

  Variable normalise_correct : forall env t tg, eval_cnf  env (normalise t tg) -> eval env t.

  Variable negate_correct : forall env t tg, eval_cnf env (negate t tg) -> ~ eval env t.

  Lemma xcnf_correct : forall (f : @GFormula Term Prop Annot unit)  pol env, eval_cnf env (xcnf pol f) -> eval_f (fun x => x) (eval env) (if pol then f else N f).
  Proof.
    induction f.
    (* TT *)
    unfold eval_cnf.
    simpl.
    destruct pol ; simpl ; auto.
    (* FF *)
    unfold eval_cnf.
    destruct pol; simpl ; auto.
    unfold eval_clause ; simpl.
    tauto.
    (* P *)
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
    (* A *)
    simpl.
    destruct pol ; simpl.
    intros.
    eapply normalise_correct  ; eauto.
    (* A 2 *)
    intros.
    eapply  negate_correct ; eauto.
    auto.
    (* Cj *)
    destruct pol ; simpl.
    (* pol = true *)
    intros.
    unfold and_cnf in H.
    destruct (eval_cnf_app  _ _ _ H).
    clear H.
    split.
    apply (IHf1 _ _ H0).
    apply (IHf2 _ _ H1).
    (* pol = false *)
    intros.
    destruct (or_cnf_correct _ _ _ H).
    generalize (IHf1 false  env H0).
    simpl.
    tauto.
    generalize (IHf2 false  env H0).
    simpl.
    tauto.
    (* D *)
    simpl.
    destruct pol.
    (* pol = true *)
    intros.
    destruct (or_cnf_correct _ _ _ H).
    generalize (IHf1 _  env H0).
    simpl.
    tauto.
    generalize (IHf2 _  env H0).
    simpl.
    tauto.
    (* pol = true *)
    unfold and_cnf.
    intros.
    destruct (eval_cnf_app  _ _ _ H).
    clear H.
    simpl.
    generalize (IHf1 _ _ H0).
    generalize (IHf2 _ _ H1).
    simpl.
    tauto.
    (**)
    simpl.
    destruct pol ; simpl.
    intros.
    apply (IHf false) ; auto.
    intros.
    generalize (IHf _ _ H).
    tauto.
    (* I *)
    simpl; intros.
    destruct pol.
    simpl.
    intro.
    destruct (or_cnf_correct _ _ _ H).
    generalize (IHf1 _ _ H1).
    simpl in *.
    tauto.
    generalize (IHf2 _ _ H1).
    auto.
    (* pol = false *)
    unfold and_cnf in H.
    simpl in H.
    destruct (eval_cnf_app _ _ _ H).
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
