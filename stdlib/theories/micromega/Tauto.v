(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

(** Formulae are either interpreted over Prop or bool. *)
Inductive kind : Type :=
|isProp
|isBool.

Register isProp as micromega.kind.isProp.
Register isBool as micromega.kind.isBool.

Inductive Trace (A : Type) :=
| null : Trace A
| push : A -> Trace A -> Trace A
| merge : Trace A -> Trace A -> Trace A
.

Section S.
  Context {TA  : Type}. (* type of interpreted atoms *)
  Context {TX  : kind -> Type}. (* type of uninterpreted terms (Prop) *)
  Context {AA  : Type}. (* type of annotations for atoms *)
  Context {AF  : Type}. (* type of formulae identifiers *)

  Inductive GFormula  : kind -> Type :=
  | TT   : forall (k: kind), GFormula k
  | FF   : forall (k: kind), GFormula k
  | X    : forall (k: kind), TX k -> GFormula k
  | A    : forall (k: kind), TA -> AA -> GFormula k
  | AND  : forall (k: kind), GFormula k -> GFormula k -> GFormula k
  | OR   : forall (k: kind), GFormula k -> GFormula k -> GFormula k
  | NOT  : forall (k: kind), GFormula k -> GFormula k
  | IMPL : forall (k: kind), GFormula k -> option AF -> GFormula k -> GFormula k
  | IFF  : forall (k: kind), GFormula k -> GFormula k -> GFormula k
  | EQ   : GFormula isBool -> GFormula isBool -> GFormula isProp.

  Register TT as micromega.GFormula.TT.
  Register FF as micromega.GFormula.FF.
  Register X  as micromega.GFormula.X.
  Register A  as micromega.GFormula.A.
  Register AND as micromega.GFormula.AND.
  Register OR  as micromega.GFormula.OR.
  Register NOT  as micromega.GFormula.NOT.
  Register IMPL  as micromega.GFormula.IMPL.
  Register IFF  as micromega.GFormula.IFF.
  Register EQ  as micromega.GFormula.EQ.


  Section MAPX.
    Variable F : forall k, TX k -> TX k.

    Fixpoint mapX (k:kind) (f : GFormula k) : GFormula k :=
      match f with
      | TT k => TT k
      | FF k => FF k
      | X x => X (F  x)
      | A k a an => A k a an
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

    Fixpoint foldA (k: kind) (f : GFormula k) (acc : ACC) : ACC :=
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

  Fixpoint ids_of_formula (k: kind) (f:GFormula k) :=
    match f with
    | IMPL f id f' => cons_id id (ids_of_formula f')
    |  _           => nil
    end.

  Fixpoint collect_annot (k: kind) (f : GFormula k) : list AA :=
    match f with
    | TT _ | FF _ | X _ => nil
    | A _ _ a => a ::nil
    | AND f1 f2
    | OR  f1 f2
    | IFF f1 f2 | EQ f1 f2
    | IMPL f1 _ f2  => collect_annot f1 ++ collect_annot f2
    | NOT  f  => collect_annot f
    end.

  Definition rtyp (k: kind) : Type := if k then Prop else bool.

  Variable ex : forall (k: kind), TX k -> rtyp k. (* [ex] will be the identity *)

  Section EVAL.

    Variable ea : forall (k: kind), TA -> rtyp k.

    Definition eTT (k: kind) : rtyp k :=
      if k as k' return  rtyp k' then True else true.

    Definition eFF (k: kind) : rtyp k :=
      if k as k' return  rtyp k' then False else false.

    Definition eAND (k: kind) : rtyp k -> rtyp k -> rtyp k :=
      if k as k' return rtyp k' -> rtyp k' -> rtyp k'
      then and else andb.

    Definition eOR (k: kind) : rtyp k -> rtyp k -> rtyp k :=
      if k as k' return rtyp k' -> rtyp k' -> rtyp k'
      then or else orb.

    Definition eIMPL (k: kind) : rtyp k -> rtyp k -> rtyp k :=
      if k as k' return rtyp k' -> rtyp k' -> rtyp k'
      then (fun x y => x -> y) else implb.

    Definition eIFF (k: kind) : rtyp k -> rtyp k -> rtyp k :=
      if k as k' return rtyp k' -> rtyp k' -> rtyp k'
      then iff else eqb.

    Definition eNOT (k: kind) : rtyp k -> rtyp k :=
      if k as k' return rtyp k' -> rtyp k'
      then not else negb.

    Fixpoint eval_f (k: kind) (f:GFormula k) {struct f}: rtyp k :=
      match f in GFormula k' return rtyp k' with
      | TT tk => eTT tk
      | FF tk => eFF tk
      | A k a _ =>  ea k a
      | X p => ex  p
      | @AND k e1 e2 => eAND k (eval_f  e1) (eval_f e2)
      | @OR k e1 e2  => eOR k (eval_f e1) (eval_f e2)
      | @NOT k e     => eNOT k (eval_f e)
      | @IMPL k f1 _ f2 => eIMPL k (eval_f f1)  (eval_f f2)
      | @IFF k f1 f2    => eIFF k (eval_f f1) (eval_f f2)
      | EQ f1 f2    => (eval_f f1) = (eval_f f2)
      end.

    Lemma eval_f_rew : forall k (f:GFormula k),
        eval_f f =
        match f in GFormula k' return rtyp k' with
        | TT tk => eTT tk
        | FF tk => eFF tk
        | A k a _ =>  ea k a
        | X p => ex  p
        | @AND k e1 e2 => eAND k (eval_f  e1) (eval_f e2)
        | @OR k e1 e2  => eOR k (eval_f e1) (eval_f e2)
        | @NOT k e     => eNOT k (eval_f e)
        | @IMPL k f1 _ f2 => eIMPL k (eval_f f1)  (eval_f f2)
        | @IFF k f1 f2    => eIFF k (eval_f f1) (eval_f f2)
        | EQ f1 f2    => (eval_f f1) = (eval_f f2)
        end.
    Proof.
      intros k f; destruct f ; reflexivity.
    Qed.

  End EVAL.


  Definition hold (k: kind) : rtyp k ->  Prop :=
    if k as k0 return (rtyp k0 -> Prop) then fun x  => x else is_true.

  Definition eiff (k: kind) : rtyp k -> rtyp k -> Prop :=
    if k as k' return rtyp k' -> rtyp k' -> Prop then iff else @eq bool.

  Lemma eiff_refl (k: kind) (x : rtyp k) :
      eiff k x x.
  Proof.
    destruct k ; simpl; tauto.
  Qed.

  Lemma eiff_sym k (x y : rtyp k) : eiff k x y -> eiff k y x.
  Proof.
    destruct k ; simpl; intros ; intuition.
  Qed.

  Lemma eiff_trans k (x y z : rtyp k) : eiff k x y -> eiff k y z -> eiff k x z.
  Proof.
    destruct k ; simpl; intros ; intuition congruence.
  Qed.

  Lemma hold_eiff (k: kind) (x y : rtyp k) :
      (hold k x <-> hold k y) <-> eiff k x y.
  Proof.
    destruct k ; simpl.
    - tauto.
    - unfold is_true.
      destruct x,y ; intuition congruence.
  Qed.

  Instance eiff_eq (k: kind) : Equivalence (eiff k).
  Proof.
    constructor.
    - exact (eiff_refl k).
    - exact (eiff_sym k).
    - exact (eiff_trans k).
  Qed.

  Add Parametric Morphism (k: kind) : (@eAND k) with signature eiff k ==> eiff k ==> eiff k as eAnd_morph.
  Proof.
    intros.
    destruct k ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (k: kind) : (@eOR k) with signature eiff k ==> eiff k ==> eiff k as eOR_morph.
  Proof.
    intros.
    destruct k ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (k: kind) : (@eIMPL k) with signature eiff k ==> eiff k ==> eiff k as eIMPL_morph.
  Proof.
    intros.
    destruct k ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (k: kind) : (@eIFF k) with signature eiff k ==> eiff k ==> eiff k as eIFF_morph.
  Proof.
    intros.
    destruct k ; simpl in *; intuition congruence.
  Qed.

  Add Parametric Morphism (k: kind) : (@eNOT k) with signature eiff k ==> eiff k as eNOT_morph.
  Proof.
    intros.
    destruct k ; simpl in *; intuition congruence.
  Qed.

  Lemma eval_f_morph :
    forall  (ev ev' : forall (k: kind), TA -> rtyp k),
      (forall k a, eiff k (ev k a) (ev' k a)) ->
      forall (k: kind)(f : GFormula k),
        (eiff k (eval_f ev f) (eval_f ev' f)).
  Proof.
    intros ev ev' H k f;
     induction f as [| | | |? ? IHf1 ? IHf2|? ? IHf1 ? IHf2|? ? IHf
                    |? ? IHf1 ? ? IHf2|? ? IHf1 ? IHf2|];
     simpl.
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
Definition eKind (k: kind) := if k then Prop else bool.
Register eKind as micromega.eKind.

Definition BFormula (A : Type) := @GFormula A eKind unit unit.

Register BFormula as micromega.BFormula.type.

Section MAPATOMS.
  Context {TA TA':Type}.
  Context {TX  : kind -> Type}.
  Context {AA  : Type}.
  Context {AF  : Type}.


  Fixpoint map_bformula (k: kind)(fct : TA -> TA') (f : @GFormula TA TX AA AF k) : @GFormula TA' TX AA AF k:=
    match f with
    | TT k => TT k
    | FF k => FF k
    | X k p => X k p
    | A k a t => A k (fct a) t
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
  intros A B f l; destruct l ; reflexivity.
Qed.


Section S.
  (** A cnf tracking annotations of atoms. *)

  (** Type parameters *)
  Variable Env   : Type.
  Variable Term  : Type.
  Variable Term' : Type.
  Variable Annot : Type.

  Local Notation Trace := (Trace Annot).

  Variable unsat : Term'  -> bool. (* see [unsat_prop] *)
  Variable deduce : Term' -> Term' -> option Term'. (* see [deduce_prop] *)

  Local Notation null := (@null Annot).
  Local Notation push := (@push Annot).
  Local Notation merge := (@merge Annot).

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
  Definition TFormula (TX: kind -> Type) (AF: Type) := @GFormula Term TX Annot AF.


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
    Context {TX : kind -> Type}.
    Context {AF : Type}.

    Variable REC : forall (pol : bool) (k: kind) (f : TFormula TX AF k), cnf.

    Definition mk_and (k: kind) (pol:bool) (f1 f2 : TFormula TX AF k):=
      (if pol then and_cnf_opt else or_cnf_opt) (REC pol f1) (REC pol f2).

    Definition mk_or (k: kind) (pol:bool) (f1 f2 : TFormula TX AF k):=
      (if pol then or_cnf_opt else and_cnf_opt) (REC pol f1) (REC pol f2).

    Definition mk_impl (k: kind) (pol:bool) (f1 f2 : TFormula TX AF k):=
      (if pol then or_cnf_opt else and_cnf_opt) (REC (negb pol) f1) (REC pol f2).


    Definition mk_iff (k: kind) (pol:bool) (f1 f2: TFormula TX AF k):=
      or_cnf_opt (and_cnf_opt (REC (negb pol) f1) (REC false f2))
                 (and_cnf_opt (REC pol f1) (REC true f2)).


  End REC.

  Definition is_bool {TX : kind -> Type} {AF: Type} (k: kind) (f : TFormula TX AF k) :=
    match f with
    | TT _ => Some true
    | FF _ => Some false
    | _    => None
    end.

  Lemma is_bool_inv : forall {TX : kind -> Type} {AF: Type} (k: kind) (f : TFormula  TX AF k) res,
      is_bool f = Some res -> f = if res then TT _ else FF _.
  Proof.
    intros TX AF k f res H.
    destruct f ; inversion H; reflexivity.
  Qed.


  Fixpoint xcnf {TX : kind -> Type} {AF: Type} (pol : bool) (k: kind) (f : TFormula TX AF k)  {struct f}: cnf :=
    match f with
    | TT _ => if pol then cnf_tt else cnf_ff
    | FF _ => if pol then cnf_ff else cnf_tt
    | X _ p => if pol then cnf_ff else cnf_ff (* This is not complete - cannot negate any proposition *)
    | A _ x t => if pol then normalise x  t else negate x  t
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

    Fixpoint radd_term (t : Term' * Annot) (cl : clause) : clause + Trace :=
      match cl with
      | nil => (* if t is unsat, the clause is empty BUT t is needed. *)
        match deduce (fst t) (fst t) with
        | Some u => if unsat u then inr (push (snd t) null) else inl (t::nil)
        | None   => inl (t::nil)
        end
      | t'::cl => (* if t /\ t' is unsat, the clause is empty BUT t & t' are needed *)
        match deduce (fst t) (fst t') with
        | Some u => if unsat u then inr (push (snd t) (push (snd t') null))
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
                        | inr l => (acc,merge tg l)
                        end) f (nil, null).

    Definition ror_clause_cnf t f :=
      match t with
      | nil => (f, null)
      | _   => xror_clause_cnf t f
      end.


    Fixpoint ror_cnf (f f':list clause) :=
      match f with
      | nil => (cnf_tt, null)
      | e :: rst =>
        let (rst_f',t) := ror_cnf rst f' in
        let (e_f', t') := ror_clause_cnf e f' in
        (rst_f' +++ e_f', merge t t')
      end.

    Definition annot_of_clause (l : clause) : list Annot :=
      List.map snd l.

    Definition annot_of_cnf (f : cnf) : list Annot :=
      List.fold_left (fun acc e => annot_of_clause e +++ acc ) f nil.


    Definition ror_cnf_opt f1 f2 :=
      if is_cnf_tt f1
      then (cnf_tt, null)
      else if is_cnf_tt f2
           then (cnf_tt, null)
           else if is_cnf_ff f2
                then (f1, null)
                else ror_cnf f1 f2.


    Definition ocons {A : Type} (o : option A) (l : list A) : list A :=
      match o with
      | None => l
      | Some e => e ::l
      end.

    Definition ratom (c : cnf) (a : Annot) : cnf * Trace :=
      if is_cnf_ff c || is_cnf_tt c
      then (c,push a null)
      else (c,null). (* t is embedded in c *)

    Section REC.
      Context {TX : kind -> Type} {AF : Type}.

      Variable RXCNF : forall (polarity: bool) (k: kind) (f: TFormula TX AF k) , cnf * Trace.

      Definition rxcnf_and (polarity:bool) (k: kind) (e1 e2 : TFormula TX AF k) :=
        let '(e1,t1) := RXCNF polarity e1 in
        let '(e2,t2) := RXCNF polarity e2 in
        if polarity
        then  (and_cnf_opt e1  e2, merge t1 t2)
        else let (f',t') := ror_cnf_opt e1 e2 in
             (f', merge t1 (merge t2 t')).

      Definition rxcnf_or (polarity:bool) (k: kind) (e1 e2 : TFormula TX AF k) :=
        let '(e1,t1) := RXCNF polarity e1 in
        let '(e2,t2) := RXCNF polarity e2 in
        if polarity
        then let (f',t') := ror_cnf_opt e1 e2 in
             (f', merge t1 (merge t2 t'))
        else (and_cnf_opt e1 e2, merge t1 t2).

      Definition rxcnf_impl (polarity:bool) (k: kind) (e1 e2 : TFormula TX AF k) :=
        let '(e1 , t1) := (RXCNF (negb polarity) e1) in
        if polarity
        then
          if is_cnf_tt e1
          then (e1,t1)
          else if is_cnf_ff e1
            then
              RXCNF polarity e2
            else (* compute disjunction *)
              let '(e2 , t2) := (RXCNF polarity e2) in
              let (f',t') := ror_cnf_opt e1 e2 in
              (f', merge t1 (merge t2 t')) (* record the hypothesis *)
        else
          let '(e2 , t2) := (RXCNF polarity e2) in
          (and_cnf_opt e1 e2, merge t1 t2).

      Definition rxcnf_iff (polarity:bool) (k: kind) (e1 e2 : TFormula TX AF k) :=
        let '(c1,t1) := RXCNF (negb polarity) e1 in
        let '(c2,t2) := RXCNF false e2 in
        let '(c3,t3) := RXCNF polarity e1 in
        let '(c4,t4) := RXCNF true e2 in
        let (f',t') := ror_cnf_opt (and_cnf_opt c1 c2) (and_cnf_opt c3 c4) in
        (f', merge t1 (merge t2 (merge t3 (merge t4 t'))))
      .

    End REC.

    Fixpoint rxcnf {TX : kind -> Type} {AF: Type}(polarity : bool) (k: kind) (f : TFormula TX AF k) : cnf * Trace :=

      match f with
      | TT _ => if polarity then (cnf_tt, null) else (cnf_ff, null)
      | FF _  => if polarity then (cnf_ff, null) else (cnf_tt, null)
      | X b p => if polarity then (cnf_ff, null) else (cnf_ff, null)
      | A _ x t  => ratom (if polarity then normalise x t else negate x t) t
      | NOT e  => rxcnf (negb polarity) e
      | AND e1 e2 => rxcnf_and rxcnf polarity e1 e2
      | OR e1 e2  => rxcnf_or rxcnf polarity e1 e2
      | IMPL e1 a e2 => rxcnf_impl rxcnf polarity e1 e2
      | IFF e1 e2 => rxcnf_iff rxcnf polarity e1 e2
      | EQ e1 e2  => rxcnf_iff rxcnf polarity e1 e2
      end.

    Section Abstraction.
      Variable TX : kind -> Type.
      Variable AF : Type.

      Class to_constrT : Type :=
        {
          mkTT   : forall (k: kind), TX k;
          mkFF   : forall (k: kind), TX k;
          mkA    : forall (k: kind), Term -> Annot -> TX k;
          mkAND  : forall (k: kind), TX k -> TX k -> TX k;
          mkOR   : forall (k: kind), TX k -> TX k -> TX k;
          mkIMPL : forall (k: kind), TX k -> TX k -> TX k;
          mkIFF  : forall (k: kind), TX k -> TX k -> TX k;
          mkNOT  : forall (k: kind), TX k -> TX k;
          mkEQ   : TX isBool -> TX isBool -> TX isProp

        }.

      Context {to_constr : to_constrT}.

      Fixpoint aformula (k: kind) (f : TFormula TX AF k) : TX k :=
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


      Definition is_X (k: kind) (f : TFormula TX AF k) : option (TX k) :=
        match f with
        | X _ p => Some p
        | _   => None
        end.

      Lemma is_X_inv : forall (k: kind) (f: TFormula TX AF k) x,
          is_X f = Some x -> f = X k x.
      Proof.
        intros k f; destruct f ; simpl ; try congruence.
      Qed.

      Variable needA : Annot -> bool.

      Definition abs_and (k: kind) (f1 f2 : TFormula TX AF k)
                 (c : forall (k: kind), TFormula TX AF k -> TFormula TX AF k -> TFormula TX AF k) :=
        match is_X f1 , is_X f2 with
        | Some _  , _ | _ , Some _ => X k (aformula  (c k f1  f2))
        |   _     , _ => c k f1 f2
        end.

      Definition abs_or (k: kind) (f1 f2 : TFormula TX AF k)
                 (c : forall (k: kind), TFormula TX AF k -> TFormula TX AF k -> TFormula TX AF k) :=
        match is_X f1 , is_X f2 with
        | Some _  , Some _ => X k (aformula (c k f1  f2))
        |   _     , _ => c k f1 f2
        end.

      Definition abs_not (k: kind) (f1 : TFormula TX AF k)
                 (c : forall (k: kind), TFormula TX AF k -> TFormula TX AF k) :=
        match is_X f1 with
        | Some _   => X k (aformula (c k f1 ))
        |   _  => c k f1
        end.


      Definition mk_arrow (o : option AF) (k: kind) (f1 f2: TFormula TX AF k) :=
        match o with
        | None => IMPL f1 None f2
        | Some _ => if is_X f1 then f2 else IMPL f1 o f2
        end.

      Fixpoint abst_simpl  (k: kind) (f : TFormula TX AF k) : TFormula TX AF k:=
        match f  with
        | TT k => TT k
        | FF k =>  FF k
        | X k p => X k p
        | A k x t => if needA t then A k x t else X k (mkA k x t)
        | AND f1 f2 => AND (abst_simpl f1) (abst_simpl f2)
        | OR f1 f2 =>  OR (abst_simpl f1) (abst_simpl f2)
        | IMPL f1 o f2 => IMPL (abst_simpl f1) o (abst_simpl f2)
        | NOT f => NOT (abst_simpl f)
        | IFF f1 f2 => IFF (abst_simpl f1) (abst_simpl f2)
        | EQ f1 f2  => EQ (abst_simpl f1) (abst_simpl f2)
        end.

      Section REC.
        Variable REC : forall (pol : bool) (k: kind) (f : TFormula TX AF k), TFormula TX AF k.

        Definition abst_and (pol : bool) (k: kind) (f1 f2:TFormula TX AF k) : TFormula TX AF k:=
          (if pol then abs_and else abs_or) k (REC pol f1) (REC pol f2) AND.

        Definition abst_or (pol : bool) (k: kind) (f1 f2:TFormula TX AF k) : TFormula TX AF k:=
          (if pol then abs_or else abs_and) k (REC pol f1) (REC pol f2) OR.

        Definition abst_impl (pol : bool) (o :option AF) (k: kind) (f1 f2:TFormula TX AF k) : TFormula TX AF k:=
          (if pol then abs_or else abs_and) k (REC (negb pol) f1) (REC pol f2) (mk_arrow o).

        Definition or_is_X (k: kind) (f1 f2: TFormula TX AF k) : bool :=
          match is_X f1 , is_X f2 with
          | Some _ , _
          | _ , Some _ => true
          |  _ , _     => false
          end.

        Definition abs_iff  (k: kind) (nf1  ff2 f1 tf2 : TFormula TX AF k) (r: kind) (def : TFormula TX AF r) : TFormula TX AF r :=
          if andb (or_is_X nf1 ff2) (or_is_X f1 tf2)
          then X r (aformula def)
          else def.


        Definition abst_iff (pol : bool) (k: kind) (f1 f2: TFormula TX AF k) : TFormula TX AF k :=
          abs_iff   (REC (negb pol) f1) (REC false f2) (REC pol f1) (REC true f2) (IFF (abst_simpl f1) (abst_simpl f2)).

        Definition abst_eq (pol : bool)  (f1 f2: TFormula TX AF isBool) : TFormula TX AF isProp :=
          abs_iff   (REC (negb pol) f1) (REC false f2) (REC pol f1) (REC true f2) (EQ (abst_simpl f1) (abst_simpl f2)).

      End REC.

      Fixpoint abst_form  (pol : bool) (k: kind) (f : TFormula TX AF k) : TFormula TX AF k:=
        match f  with
        | TT k => if pol then TT k else X k (mkTT k)
        | FF k => if pol then X k (mkFF k) else FF k
        | X k p => X k p
        | A k x t => if needA t then A k x t else X k (mkA k x t)
        | AND f1 f2 => abst_and abst_form pol f1 f2
        | OR f1 f2 =>  abst_or abst_form pol f1 f2
        | IMPL f1 o f2 => abst_impl abst_form pol o f1 f2
        | NOT f => abs_not  (abst_form (negb pol) f) NOT
        | IFF f1 f2 => abst_iff abst_form  pol f1 f2
        | EQ f1 f2  => abst_eq abst_form pol f1 f2
        end.

      Lemma if_same : forall {A: Type} (b: bool) (t:A),
          (if b then t else t) = t.
      Proof.
        intros A b; destruct b ; reflexivity.
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
        intros f1; destruct f1 ; simpl ; try congruence.
      Qed.

      Lemma is_cnf_ff_inv : forall f1,
          is_cnf_ff f1 = true -> f1 = cnf_ff.
      Proof.
        unfold cnf_ff.
        intros f1 ; destruct f1 as [|c f1] ; simpl ; try congruence.
        destruct c ; simpl ; try congruence.
        destruct f1 ; try congruence.
        reflexivity.
      Qed.


      Lemma if_cnf_tt : forall f, (if is_cnf_tt f then cnf_tt else f) = f.
      Proof.
        intros f.
        destruct (is_cnf_tt f) eqn:EQ.
        - apply is_cnf_tt_inv in EQ;auto.
        - reflexivity.
      Qed.

      Lemma or_cnf_opt_cnf_ff : forall f,
          or_cnf_opt cnf_ff f = f.
      Proof.
        intros f.
        unfold or_cnf_opt.
        rewrite is_cnf_tt_cnf_ff.
        simpl.
        destruct (is_cnf_tt f) eqn:EQ.
        - apply is_cnf_tt_inv in EQ.
          congruence.
        - destruct (is_cnf_ff f) eqn:EQ1.
          + apply is_cnf_ff_inv in EQ1.
            congruence.
          + reflexivity.
      Qed.

      Lemma abs_and_pol : forall (k: kind) (f1 f2: TFormula TX AF k) pol,
          and_cnf_opt (xcnf pol f1) (xcnf pol f2) =
          xcnf pol (abs_and f1 f2 (if pol then AND else OR)).
      Proof.
        unfold abs_and; intros k f1 f2 pol.
        destruct (is_X f1) eqn:EQ1.
        - apply is_X_inv in EQ1.
          subst.
          simpl.
          rewrite if_same. reflexivity.
        - destruct (is_X f2) eqn:EQ2.
          + apply is_X_inv in EQ2.
            subst.
            simpl.
            rewrite if_same.
            unfold and_cnf_opt.
            rewrite orb_comm. reflexivity.
          + destruct pol ; simpl; auto.
      Qed.

      Lemma abs_or_pol : forall (k: kind) (f1 f2:TFormula TX AF k) pol,
          or_cnf_opt (xcnf pol f1) (xcnf pol f2) =
          xcnf pol (abs_or f1 f2 (if pol then OR else AND)).
      Proof.
        unfold abs_or; intros k f1 f2 pol.
        destruct (is_X f1) eqn:EQ1.
        - apply is_X_inv in EQ1.
          subst.
          destruct (is_X f2) eqn:EQ2.
          + apply is_X_inv in EQ2.
            subst.
            simpl.
            rewrite if_same.
            reflexivity.
          + simpl.
            rewrite if_same.
            destruct pol ; simpl; auto.
        - destruct pol ; simpl ; auto.
      Qed.

      Variable needA_all : forall a, needA a = true.

      Lemma xcnf_true_mk_arrow_l : forall b o t (f:TFormula TX AF b),
          xcnf true (mk_arrow o (X b t) f) = xcnf true f.
      Proof.
        intros b o; destruct o ; simpl; auto.
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
        intros b o; destruct o ; simpl; auto.
        - intros t f.
          destruct (is_X f) eqn:EQ.
          + apply is_X_inv in EQ. subst. reflexivity.
          + simpl.
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
        intros f.
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
        intros b f; induction f ; simpl ; auto.
        rewrite needA_all.
        reflexivity.
      Qed.

      Lemma abst_simpl_correct : forall b (f:TFormula TX AF b) pol,
          xcnf pol f = xcnf pol (abst_simpl f).
      Proof.
        intros b f;
          induction f as [| | | |? ? IHf1 f2 IHf2|? ? IHf1 f2 IHf2
            |? ? IHf|? ? IHf1 ? f2 IHf2|? ? IHf1 f2 IHf2|f1 IHf1 f2 IHf2];
          simpl;intros;
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

      Ltac is_X t :=
        match goal with
        | |-context[is_X ?X] =>
          let f := fresh "EQ" in
          destruct (is_X X) as [t|] eqn:f ;
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

      Lemma or_is_X_inv : forall (k: kind) (f1 f2 : TFormula TX AF k),
          or_is_X f1 f2 = true ->
          exists k1, is_X f1 = Some k1 \/ is_X f2 = Some k1.
      Proof.
        unfold or_is_X.
        intros k f1 f2.
        is_X t; is_X t0.
        - exists t ; intuition.
        - exists t ; intuition.
        - exists t0 ; intuition.
        - congruence.
      Qed.

      Lemma mk_iff_is_bool : forall (k: kind) (f1 f2:TFormula TX AF k) pol,
          match is_bool f2 with
          | Some isb => xcnf (if isb then pol else negb pol) f1
          | None => mk_iff xcnf pol f1 f2
          end = mk_iff xcnf pol f1 f2.
      Proof.
        intros k f1 f2 pol.
        destruct (is_bool f2) as [b|] eqn:EQ; auto.
        apply is_bool_inv in EQ.
        subst.
        unfold mk_iff.
        destruct b ; simpl; cnf_simpl; reflexivity.
      Qed.

      Lemma abst_iff_correct : forall
          (k: kind)
          (f1 f2 : GFormula k)
          (IHf1 : forall pol : bool, xcnf pol f1 = xcnf pol (abst_form pol f1))
          (IHf2 : forall pol : bool, xcnf pol f2 = xcnf pol (abst_form pol f2))
          (pol : bool),
          xcnf pol (IFF f1 f2) = xcnf pol (abst_iff abst_form pol f1 f2).
      Proof.
        intros k f1 f2 IHf1 IHf2 pol; simpl.
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
          (f1 f2 : GFormula isBool)
          (IHf1 : forall pol : bool, xcnf pol f1 = xcnf pol (abst_form pol f1))
          (IHf2 : forall pol : bool, xcnf pol f2 = xcnf pol (abst_form pol f2))
          (pol : bool),
          xcnf pol (EQ f1 f2) = xcnf pol (abst_form pol (EQ f1 f2)).
      Proof.
        intros f1 f2 IHf1 IHf2 pol.
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
        intros b f;
         induction f as [| | | |? ? IHf1 ? IHf2|? ? IHf1 ? IHf2|? f IHf
           |? f1 IHf1 o f2 IHf2|? IHf1 ? IHf2|];
         intros pol.
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
               -- rewrite EQ1. simpl.
                  congruence.
               -- congruence.
        -  apply abst_iff_correct; auto.
        -  apply abst_eq_correct; auto.
      Qed.

    End Abstraction.


  End CNFAnnot.


  Lemma radd_term_term : forall a' a cl, radd_term a a' = inl cl -> add_term a a' = Some cl.
  Proof.
    intros a'; induction a' as [|a a' IHa']; simpl.
    - intros a cl H.
      destruct (deduce (fst a) (fst a)) as [t|].
      + destruct (unsat t).
        * congruence.
        * inversion H. reflexivity.
      + inversion H ;reflexivity.
    - intros a0 cl H.
      destruct (deduce (fst a0) (fst a)) as [t|].
      + destruct (unsat t).
        * congruence.
        * destruct (radd_term a0 a') eqn:RADD; try congruence.
          inversion H. subst.
          apply IHa' in RADD.
          rewrite RADD.
          reflexivity.
      + destruct (radd_term a0 a') eqn:RADD; try congruence.
        inversion H. subst.
        apply IHa' in RADD.
        rewrite RADD.
        reflexivity.
  Qed.

  Lemma radd_term_term' : forall a' a cl, add_term a a' = Some cl -> radd_term a a' = inl cl.
  Proof.
    intros a'; induction a' as [|a a' IHa']; simpl.
    - intros a cl H.
      destruct (deduce (fst a) (fst a)) as [t|].
      + destruct (unsat t).
        * congruence.
        * inversion H. reflexivity.
      + inversion H ;reflexivity.
    - intros a0 cl H.
      destruct (deduce (fst a0) (fst a)) as [t|].
      + destruct (unsat t).
        * congruence.
        * destruct (add_term a0 a') eqn:RADD; try congruence.
          inversion H. subst.
          apply IHa' in RADD.
          rewrite RADD.
          reflexivity.
      + destruct (add_term a0 a') eqn:RADD; try congruence.
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
    assert (ACC: fst (@nil clause, null) = nil) by reflexivity.
    intros a f.
    set (F1:= (fun '(acc, tg) (e : clause) =>
                 match ror_clause a e with
                 | inl cl => (cl :: acc, tg)
                 | inr l => (acc, merge tg l)
                 end)).
    set (F2:= (fun (acc : list clause) (e : clause) =>
                 match or_clause a e with
                 | Some cl => cl :: acc
                 | None => acc
                 end)).
    revert ACC.
    generalize (@nil clause, null).
    generalize (@nil clause).
    induction f as [|a0 f IHf]; simpl ; auto.
    intros ? p ?.
    apply IHf.
    unfold F1 , F2.
    destruct p ; simpl in * ; subst.
    clear.
    revert a0.
    induction a as [|a a0 IHa]; simpl; auto.
    intros a1.
    destruct (radd_term a a1) eqn:RADD.
    - apply radd_term_term in RADD.
      rewrite RADD.
      auto.
    - destruct (add_term a a1) eqn:RADD'.
      + apply radd_term_term' in RADD'.
        congruence.
      + reflexivity.
  Qed.

  Lemma ror_clause_clause : forall a f,
      fst (ror_clause_cnf a f) = or_clause_cnf a f.
  Proof.
    unfold ror_clause_cnf,or_clause_cnf.
    intros a; destruct a ; auto.
    apply xror_clause_clause.
  Qed.

  Lemma ror_cnf_cnf : forall f1 f2, fst (ror_cnf f1 f2) = or_cnf f1 f2.
  Proof.
    intros f1; induction f1 as [|a f1 IHf1] ; simpl ; auto.
    intros f2.
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
    intros f1 f2.
    destruct (is_cnf_tt f1).
    - simpl ; auto.
    - simpl. destruct (is_cnf_tt f2) ; simpl ; auto.
      destruct (is_cnf_ff f2) eqn:EQ.
      + reflexivity.
      + apply ror_cnf_cnf.
  Qed.

  Lemma ratom_cnf : forall  f a,
      fst (ratom f a) = f.
  Proof.
    unfold ratom.
    intros f a.
    destruct (is_cnf_ff f || is_cnf_tt f); auto.
  Qed.

  Lemma rxcnf_and_xcnf : forall {TX : kind -> Type} {AF:Type} (k: kind) (f1 f2:TFormula TX AF k)
                                (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
                                (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
      forall pol : bool, fst (rxcnf_and rxcnf pol f1 f2) = mk_and xcnf pol f1 f2.
  Proof.
    intros TX AF k f1 f2 IHf1 IHf2 pol.
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
    forall {TX : kind -> Type} {AF:Type} (k: kind) (f1 f2:TFormula TX AF k)
           (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
           (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
    forall pol : bool, fst (rxcnf_or rxcnf pol f1 f2) = mk_or xcnf pol f1 f2.
  Proof.
    intros TX AF k f1 f2 IHf1 IHf2 pol.
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
    forall {TX : kind -> Type} {AF:Type} (k: kind) (f1 f2:TFormula TX AF k)
           (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
           (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
    forall pol : bool, fst (rxcnf_impl rxcnf pol f1 f2) = mk_impl xcnf pol f1 f2.
  Proof.
    intros TX AF k f1 f2 IHf1 IHf2 pol.
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
    generalize (is_cnf_tt_inv (xcnf (negb true) f1)).
    destruct (is_cnf_tt (xcnf (negb true) f1)).
    + intros H.
      rewrite H by auto.
      reflexivity.
    +
      generalize (is_cnf_ff_inv (xcnf (negb true) f1)).
    destruct (is_cnf_ff (xcnf (negb true) f1)).
    * intros H.
      rewrite H by auto.
      unfold or_cnf_opt.
      simpl.
      destruct (is_cnf_tt (xcnf true f2)) eqn:EQ;auto.
      -- apply is_cnf_tt_inv in EQ; auto.
      -- destruct (is_cnf_ff (xcnf true f2)) eqn:EQ1.
         ++ apply is_cnf_ff_inv in EQ1. congruence.
         ++ reflexivity.
    *
      rewrite <- ror_opt_cnf_cnf.
      destruct (ror_cnf_opt (xcnf (negb true) f1) (xcnf true f2)).
      intros.
      reflexivity.
  Qed.

  Lemma rxcnf_iff_xcnf :
    forall {TX : kind -> Type} {AF:Type} (k: kind) (f1 f2:TFormula TX AF k)
           (IHf1 : forall pol : bool, fst (rxcnf pol f1) = xcnf pol f1)
           (IHf2 : forall pol : bool, fst (rxcnf pol f2) = xcnf pol f2),
    forall pol : bool, fst (rxcnf_iff rxcnf pol f1 f2) = mk_iff xcnf pol f1 f2.
  Proof.
    intros TX AF k f1 f2 IHf1 IHf2 pol.
    unfold rxcnf_iff.
    unfold mk_iff.
    rewrite <- (IHf1 (negb pol)).
    rewrite <- (IHf1 pol).
    rewrite <- (IHf2 false).
    rewrite <- (IHf2 true).
    destruct (rxcnf (negb pol) f1) as [c ?].
    destruct (rxcnf false f2) as [c0 ?].
    destruct (rxcnf pol f1) as [c1 ?].
    destruct (rxcnf true f2) as [c2 ?].
    destruct (ror_cnf_opt (and_cnf_opt c c0) (and_cnf_opt c1 c2)) as [c3 l3] eqn:EQ.
    simpl.
    change c3 with (fst (c3,l3)).
    rewrite <- EQ. rewrite ror_opt_cnf_cnf.
    reflexivity.
  Qed.

  Lemma rxcnf_xcnf : forall {TX : kind -> Type} {AF:Type} (k: kind) (f:TFormula TX AF k) pol,
      fst (rxcnf  pol f) = xcnf pol f.
  Proof.
    intros TX AF k f; induction f ; simpl ; auto; intros pol.
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
  Proof using.
    clear.
    unfold cnf_ff, eval_cnf,eval_clause.
    simpl. tauto.
  Qed.

  Lemma eval_cnf_tt : forall env, eval_cnf env cnf_tt <-> True.
  Proof using.
    clear.
    unfold cnf_tt, eval_cnf,eval_clause.
    simpl. tauto.
  Qed.

  Lemma eval_cnf_and_opt : forall env x y, eval_cnf env (and_cnf_opt x y) <-> eval_cnf env (and_cnf x y).
  Proof.
    unfold and_cnf_opt.
    intros env x y.
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
    intros env t cl; induction cl as [|a cl IHcl].
    - (* BC *)
      simpl.
      case_eq (deduce (fst t) (fst t)) ; try tauto.
      intros t0 H.
      generalize (@deduce_prop _ _ _ H env).
      case_eq (unsat t0) ; try tauto.
      { intros H0 ?.
        generalize (@unsat_prop _ H0 env).
        unfold eval_clause.
        rewrite make_conj_cons.
        simpl; intros.
        tauto.
      }
    - (* IC *)
      simpl.
      case_eq (deduce (fst t) (fst a));
        intros t0; [intros H|].
      + generalize (@deduce_prop _ _ _ H env).
        case_eq (unsat t0); intros H0 H1.
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
      + destruct (add_term t cl) ; simpl in *;
          unfold eval_clause in * ;
          repeat rewrite make_conj_cons in *; tauto.
  Qed.


  Lemma no_middle_eval_tt : forall env a,
      eval_tt env a \/ ~ eval_tt env a.
  Proof.
    unfold eval_tt.
    auto.
  Qed.

  #[local]
  Hint Resolve no_middle_eval_tt : tauto.

  Lemma or_clause_correct : forall cl cl' env,  eval_opt_clause env (or_clause cl cl') <-> eval_clause env cl \/ eval_clause env cl'.
  Proof.
    intros cl; induction cl as [|a cl IHcl].
    - simpl. unfold eval_clause at 2.  simpl. tauto.
    - intros cl' env.
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
    intros env t.
    set (F := (fun (acc : list clause) (e : clause)  =>
                 match or_clause t e with
                 | Some cl => cl :: acc
                 | None => acc
                 end)).
    intro f.
    assert (  make_conj (eval_clause env) (fold_left F f nil) <-> (eval_clause env t \/ make_conj (eval_clause env) f) /\ make_conj (eval_clause env) nil) as H.
    {
      generalize (@nil clause) as acc.
      induction f as [|a f IHf].
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
  Proof using.
    intros; clear.
    unfold eval_cnf in *.
    rewrite make_conj_cons ; eauto.
    unfold eval_clause.
    tauto.
  Qed.


  Lemma or_cnf_correct : forall env f f', eval_cnf env (or_cnf f f') <-> (eval_cnf env  f) \/ (eval_cnf  env f').
  Proof.
    intros env f; induction f as [|a f IHf].
    - unfold eval_cnf.
      simpl.
      tauto.
      (**)
    - intros.
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
    intros env f f'.
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
      - apply is_cnf_ff_inv in EQ.
        subst.
        rewrite or_cnf_correct.
        rewrite eval_cnf_ff.
        tauto.
      - tauto.
    }
  Qed.

  Variable eval  : Env -> forall (k: kind), Term -> rtyp k.

  Variable normalise_correct : forall env b t tg, eval_cnf  env (normalise t tg) ->  hold b (eval env b t).

  Variable negate_correct : forall env b t tg, eval_cnf env (negate t tg) -> hold b (eNOT b (eval env b t)).

  Definition e_rtyp (k: kind) (x : rtyp k) : rtyp k := x.

  Lemma hold_eTT : forall k, hold k (eTT k).
  Proof.
    intros k; destruct k ; simpl; auto.
  Qed.

  #[local]
  Hint Resolve hold_eTT : tauto.

  Lemma hold_eFF : forall k,
      hold k (eNOT k (eFF k)).
  Proof.
    intros k; destruct k ; simpl;auto.
  Qed.

  #[local]
  Hint Resolve hold_eFF : tauto.

  Lemma hold_eAND : forall k r1 r2,
      hold k (eAND k r1 r2) <-> (hold k r1 /\ hold k r2).
  Proof.
    intros k; destruct k ; simpl.
    - intros. apply iff_refl.
    - apply andb_true_iff.
  Qed.

  Lemma hold_eOR : forall k r1 r2,
      hold k (eOR k r1 r2) <-> (hold k r1 \/ hold k r2).
  Proof.
    intros k; destruct k ; simpl.
    - intros. apply iff_refl.
    - apply orb_true_iff.
  Qed.

  Lemma hold_eNOT : forall k e,
      hold k (eNOT k e) <-> not (hold k e).
  Proof.
    intros k; destruct k ; simpl.
    - intros. apply iff_refl.
    - intros e. unfold is_true.
      rewrite negb_true_iff.
      destruct e ; intuition congruence.
  Qed.

  Lemma hold_eIMPL : forall k e1 e2,
      hold k (eIMPL k e1 e2) <-> (hold k e1 -> hold k e2).
  Proof.
    intros k; destruct k ; simpl.
    - intros. apply iff_refl.
    - intros e1 e2.
      unfold is_true.
      destruct e1,e2 ; simpl ; intuition congruence.
  Qed.

  Lemma hold_eIFF : forall k e1 e2,
      hold k (eIFF k e1 e2) <-> (hold k e1 <-> hold k e2).
  Proof.
    intros k; destruct k ; simpl.
    - intros. apply iff_refl.
    - intros e1 e2.
      unfold is_true.
      rewrite eqb_true_iff.
      destruct e1,e2 ; simpl ; intuition congruence.
  Qed.



  Lemma xcnf_impl :
    forall
      (k: kind)
      (f1 : GFormula k)
      (o : option unit)
      (f2 : GFormula k)
      (IHf1 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f1) ->
          hold k (eval_f e_rtyp (eval env) (if pol then f1 else NOT f1)))
      (IHf2 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f2) ->
          hold k (eval_f e_rtyp (eval env) (if pol then f2 else NOT f2))),
    forall (pol : bool) (env : Env),
      eval_cnf env (xcnf pol (IMPL f1 o f2)) ->
      hold k (eval_f e_rtyp (eval env) (if pol then IMPL f1 o f2 else NOT (IMPL f1 o f2))).
  Proof.
    simpl; intros k f1 o f2 IHf1 IHf2 pol env H. unfold mk_impl in H.
    destruct pol.
    + simpl.
      rewrite hold_eIMPL.
      intro.
      rewrite or_cnf_opt_correct in H.
      rewrite or_cnf_correct in H.
      destruct H as [H | H].
      * generalize (IHf1 _ _ H).
        simpl in *.
        rewrite hold_eNOT.
        tauto.
      * generalize (IHf2 _ _ H).
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

  Lemma hold_eIFF_IMPL : forall k e1 e2,
      hold k (eIFF k e1 e2) <-> (hold k (eAND k (eIMPL k e1 e2) (eIMPL k e2 e1))).
  Proof.
    intros.
    rewrite hold_eIFF.
    rewrite hold_eAND.
    rewrite! hold_eIMPL.
    tauto.
  Qed.

  Lemma hold_eEQ : forall e1 e2,
      hold isBool (eIFF isBool e1 e2) <-> e1 = e2.
  Proof.
    simpl.
    intros e1 e2; destruct e1,e2 ; simpl ; intuition congruence.
  Qed.


  Lemma xcnf_iff : forall
      (k : kind)
      (f1 f2 : @GFormula Term rtyp Annot unit k)
      (IHf1 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f1) ->
          hold k (eval_f e_rtyp (eval env) (if pol then f1 else NOT f1)))
      (IHf2 : forall (pol : bool) (env : Env),
          eval_cnf env (xcnf pol f2) ->
          hold k (eval_f e_rtyp (eval env) (if pol then f2 else NOT f2))),
      forall (pol : bool) (env : Env),
        eval_cnf env (xcnf pol (IFF f1 f2)) ->
        hold k (eval_f e_rtyp (eval env) (if pol then IFF f1 f2 else NOT (IFF f1 f2))).
  Proof.
    simpl.
    intros k f1 f2 IHf1 IHf2 pol env H.
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

  Lemma xcnf_correct : forall (k: kind) (f : @GFormula Term rtyp Annot unit k)  pol env,
      eval_cnf env (xcnf pol f) -> hold k (eval_f e_rtyp (eval env) (if pol then f else NOT f)).
  Proof.
    intros k f;
     induction f as [| | | |? ? IHf1 ? IHf2|? ? IHf1 ? IHf2|? ? IHf
       |? ? IHf1 ? ? IHf2|? ? IHf1 f2 IHf2|f1 IHf1 f2 IHf2];
     intros pol env H.
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
      + intros.
        eapply normalise_correct  ; eauto.
      + (* A 2 *)
        intros.
        eapply  negate_correct ; eauto.
    - (* AND *)
      destruct pol ; simpl in H.
      + (* pol = true *)
        intros.
        rewrite eval_cnf_and_opt in H.
        unfold and_cnf in H.
        rewrite eval_cnf_app  in H.
        destruct H as [H H0].
        apply hold_eAND; split.
        * apply (IHf1 _ _ H).
        * apply (IHf2 _ _ H0).
      +  (* pol = false *)
        intros.
        apply hold_eNOT.
        rewrite hold_eAND.
        rewrite or_cnf_opt_correct in H.
        rewrite or_cnf_correct in H.
        destruct H as [H | H].
        * generalize (IHf1 false  env H).
          simpl.
          rewrite hold_eNOT.
          tauto.
        * generalize (IHf2 false  env H).
          simpl.
          rewrite hold_eNOT.
          tauto.
    - (* OR *)
      simpl in H.
      destruct pol.
      + (* pol = true *)
        intros. unfold mk_or in H.
        rewrite or_cnf_opt_correct in H.
        rewrite or_cnf_correct in H.
        destruct H as [H | H].
        * generalize (IHf1 _  env H).
          simpl.
          rewrite hold_eOR.
          tauto.
        * generalize (IHf2 _  env H).
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
      + intros.
        apply (IHf false) ; auto.
      + intros.
        generalize (IHf _ _ H).
        rewrite ! hold_eNOT.
        tauto.
    - (* IMPL *)
      apply xcnf_impl; auto.
    - apply xcnf_iff ; auto.
    - simpl in H.
      destruct (is_bool f2) as [b|] eqn:EQ.
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
        * rewrite <- hold_eEQ.
          simpl; auto.
        * rewrite <- hold_eEQ.
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
    intros t; induction t as [|a t IHt].
    - (* bc *)
      simpl.
      auto.
    - (* ic *)
      simpl.
      intros w; destruct w as [|w ?].
      + intros ; discriminate.
      + case_eq (checker a w) ; intros H H0 env ** ; try discriminate.
        generalize (@checker_sound _ _ H env).
        generalize (IHt _ H0 env) ; intros H1 H2.
        destruct t.
        * red ; intro.
          rewrite <- make_conj_impl in H2.
          tauto.
        * rewrite <- make_conj_impl in H2.
          tauto.
  Qed.

  Definition tauto_checker (f:@GFormula Term rtyp Annot unit isProp) (w:list Witness) : bool :=
    cnf_checker (xcnf true f) w.

  Lemma tauto_checker_sound : forall t  w, tauto_checker t w = true -> forall env, eval_f e_rtyp (eval env)  t.
  Proof.
    unfold tauto_checker.
    intros t w H env.
    change (eval_f e_rtyp (eval env) t) with (eval_f e_rtyp (eval env) (if true then t else TT isProp)).
    apply (xcnf_correct t true).
    eapply cnf_checker_sound ; eauto.
  Qed.

  Definition eval_bf {A : Type} (ea : forall (k: kind), A -> rtyp k) (k: kind) (f: BFormula A k) := eval_f e_rtyp ea f.

  Lemma eval_bf_map : forall T U (fct: T-> U) env (k: kind) (f:BFormula T k) ,
      eval_bf env  (map_bformula fct f)  = eval_bf (fun b x => env b (fct x)) f.
  Proof.
    intros T U fct env k f;
      induction f as [| | | |? ? IHf1 ? IHf2|? ? IHf1 ? IHf2|? ? IHf
        |? ? IHf1 ? ? IHf2|? ? IHf1 ? IHf2|? IHf1 ? IHf2];
      simpl ; try (rewrite IHf1 ; rewrite IHf2) ; auto.
    rewrite <- IHf.  auto.
  Qed.


End S.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
