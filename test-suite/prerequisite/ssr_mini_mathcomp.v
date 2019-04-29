(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Some code from mathcomp needed in order to run ssr_* tests *)

Require Import ssreflect ssrfun ssrbool.

Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* eqtype ---------------------------------------------------------- *)

Module Equality.

Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : rel T; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation eqType := type.
Notation EqMixin := Mixin.
Notation EqType T m := (@pack T m).
Notation "[ 'eqMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'eqMixin'  'of'  T ]") : form_scope.
Notation "[ 'eqType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'eqType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'eqType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'eqType'  'of'  T ]") : form_scope.
End Exports.

End Equality.
Export Equality.Exports.

Definition eq_op T := Equality.op (Equality.class T).

Lemma eqE T x : eq_op x = Equality.op (Equality.class T) x.
Proof. by []. Qed.

Lemma eqP T : Equality.axiom (@eq_op T).
Proof. by case: T => ? []. Qed.
Arguments eqP [T x y].

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (~~ (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (~~ (x == y :> T))
  (at level 70, y at next level) : bool_scope.
Notation "x =P y" := (eqP : reflect (x = y) (x == y))
  (at level 70, no associativity) : eq_scope.
Notation "x =P y :> T" := (eqP : reflect (x = y :> T) (x == y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.

Prenex Implicits eq_op eqP.

Lemma eq_refl (T : eqType) (x : T) : x == x. Proof. exact/eqP. Qed.
Notation eqxx := eq_refl.

Lemma eq_sym (T : eqType) (x y : T) : (x == y) = (y == x).
Proof. exact/eqP/eqP. Qed.

Hint Resolve eq_refl eq_sym.


Definition eqb b := addb (~~ b).

Lemma eqbP : Equality.axiom eqb.
Proof. by do 2!case; constructor. Qed.

Canonical bool_eqMixin := EqMixin eqbP.
Canonical bool_eqType := Eval hnf in EqType bool bool_eqMixin.

Section ProdEqType.

Variable T1 T2 : eqType.

Definition pair_eq := [rel u v : T1 * T2 | (u.1 == v.1) && (u.2 == v.2)].

Lemma pair_eqP : Equality.axiom pair_eq.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP andP) => [[]|[<- <-]] //=.
by do 2!move/eqP->.
Qed.

Definition prod_eqMixin := EqMixin pair_eqP.
Canonical prod_eqType := Eval hnf in EqType (T1 * T2) prod_eqMixin.

End ProdEqType.

Section OptionEqType.

Variable T : eqType.

Definition opt_eq (u v : option T) : bool :=
  oapp (fun x => oapp (eq_op x) false v) (~~ v) u.

Lemma opt_eqP : Equality.axiom opt_eq.
Proof.
case=> [x|] [y|] /=; by [constructor | apply: (iffP eqP) => [|[]] ->].
Qed.

Canonical option_eqMixin := EqMixin opt_eqP.
Canonical option_eqType := Eval hnf in EqType (option T) option_eqMixin.

End OptionEqType.

Notation xpred1 := (fun a1 x => x == a1).
Notation xpredU1 := (fun a1 (p : pred _) x => (x == a1) || p x).

Section EqPred.

Variable T : eqType.

Definition pred1 (a1 : T) := SimplPred (xpred1 a1).
Definition predU1 (a1 : T) p := SimplPred (xpredU1 a1 p).

End EqPred.

Section TransferEqType.

Variables (T : Type) (eT : eqType) (f : T -> eT).

Lemma inj_eqAxiom : injective f -> Equality.axiom (fun x y => f x == f y).
Proof. by move=> f_inj x y; apply: (iffP eqP) => [|-> //]; apply: f_inj. Qed.

Definition InjEqMixin f_inj := EqMixin (inj_eqAxiom f_inj).

Definition PcanEqMixin g (fK : pcancel f g) := InjEqMixin (pcan_inj fK).

Definition CanEqMixin g (fK : cancel f g) := InjEqMixin (can_inj fK).

End TransferEqType.

(* We use the module system to circumvent a silly limitation that  *)
(* forbids using the same constant to coerce to different targets. *)
Module Type EqTypePredSig.
Parameter sort : eqType -> predArgType.
End EqTypePredSig.
Module MakeEqTypePred (eqmod : EqTypePredSig).
Coercion eqmod.sort : eqType >-> predArgType.
End MakeEqTypePred.
Module Export EqTypePred := MakeEqTypePred Equality.


Section SubType.

Variables (T : Type) (P : pred T).

Structure subType : Type := SubType {
  sub_sort :> Type;
  val : sub_sort -> T;
  Sub : forall x, P x -> sub_sort;
  _ : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
  _ : forall x Px, val (@Sub x Px) = x
}.

Arguments Sub [s].
Lemma vrefl : forall x, P x -> x = x. Proof. by []. Qed.
Definition vrefl_rect := vrefl.

Definition clone_subType U v :=
  fun sT & sub_sort sT -> U =>
  fun c Urec cK (sT' := @SubType U v c Urec cK) & phant_id sT' sT => sT'.

Variable sT : subType.

CoInductive Sub_spec : sT -> Type := SubSpec x Px : Sub_spec (Sub x Px).

Lemma SubP u : Sub_spec u.
Proof. by case: sT Sub_spec SubSpec u => T' _ C rec /= _. Qed.

Lemma SubK x Px : @val sT (Sub x Px) = x.
Proof. by case: sT. Qed.

Definition insub x :=
  if @idP (P x) is ReflectT Px then @Some sT (Sub x Px) else None.

Definition insubd u0 x := odflt u0 (insub x).

CoInductive insub_spec x : option sT -> Type :=
  | InsubSome u of P x & val u = x : insub_spec x (Some u)
  | InsubNone   of ~~ P x          : insub_spec x None.

Lemma insubP x : insub_spec x (insub x).
Proof.
by rewrite /insub; case: {-}_ / idP; [left; rewrite ?SubK | right; apply/negP].
Qed.

Lemma insubT x Px : insub x = Some (Sub x Px).
Admitted.

Lemma insubF x : P x = false -> insub x = None.
Proof. by move/idP; case: insubP. Qed.

Lemma insubN x : ~~ P x -> insub x = None.
Proof. by move/negPf/insubF. Qed.

Lemma isSome_insub : ([eta insub] : pred T) =1 P.
Proof. by apply: fsym => x; case: insubP => // /negPf. Qed.

Lemma insubK : ocancel insub (@val _).
Proof. by move=> x; case: insubP. Qed.

Lemma valP (u : sT) : P (val u).
Proof. by case/SubP: u => x Px; rewrite SubK. Qed.

Lemma valK : pcancel (@val _) insub.
Proof. by case/SubP=> x Px; rewrite SubK; apply: insubT. Qed.

Lemma val_inj : injective (@val sT).
Proof. exact: pcan_inj valK. Qed.

Lemma valKd u0 : cancel (@val _) (insubd u0).
Proof. by move=> u; rewrite /insubd valK. Qed.

Lemma val_insubd u0 x : val (insubd u0 x) = if P x then x else val u0.
Proof. by rewrite /insubd; case: insubP => [u -> | /negPf->]. Qed.

Lemma insubdK u0 : {in P, cancel (insubd u0) (@val _)}.
Proof. by move=> x Px; rewrite /= val_insubd [P x]Px. Qed.

Definition insub_eq x :=
  let Some_sub Px := Some (Sub x Px : sT) in
  let None_sub _ := None in
  (if P x as Px return P x = Px -> _ then Some_sub else None_sub) (erefl _).

Lemma insub_eqE : insub_eq =1 insub.
Proof.
rewrite /insub_eq /insub => x; case: {2 3}_ / idP (erefl _) => // Px Px'.
by congr (Some _); apply: val_inj; rewrite !SubK.
Qed.

End SubType.

Arguments SubType [T P].
Arguments Sub [T P s].
Arguments vrefl [T P].
Arguments vrefl_rect [T P].
Arguments clone_subType [T P] U v [sT] _ [c Urec cK].
Arguments insub [T P sT].
Arguments insubT [T] P [sT x].
Arguments val_inj [T P sT].
Prenex Implicits val Sub vrefl vrefl_rect insub insubd val_inj.

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Local Notation inlined_new_rect :=
  (fun K K_S u => let (x) as u return K u := u in K_S x).

Notation "[ 'subType' 'for' v ]" := (SubType _ v _ inlined_sub_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Notation "[ 'sub' 'Type' 'for' v ]" := (SubType _ v _ _ vrefl_rect)
 (at level 0, format "[ 'sub' 'Type'  'for'  v ]") : form_scope.

Notation "[ 'subType' 'for' v 'by' rec ]" := (SubType _ v _ rec vrefl)
 (at level 0, format "[ 'subType'  'for'  v  'by'  rec ]") : form_scope.

Notation "[ 'subType' 'of' U 'for' v ]" := (clone_subType U v id idfun)
 (at level 0, format "[ 'subType'  'of'  U  'for'  v ]") : form_scope.

(*
Notation "[ 'subType' 'for' v ]" := (clone_subType _ v id idfun)
 (at level 0, format "[ 'subType'  'for'  v ]") : form_scope.
*)
Notation "[ 'subType' 'of' U ]" := (clone_subType U _ id id)
 (at level 0, format "[ 'subType'  'of'  U ]") : form_scope.

Definition NewType T U v c Urec :=
  let Urec' P IH := Urec P (fun x : T => IH x isT : P _) in
  SubType U v (fun x _ => c x) Urec'.
Arguments NewType [T U].

Notation "[ 'newType' 'for' v ]" := (NewType v _ inlined_new_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Notation "[ 'new' 'Type' 'for' v ]" := (NewType v _ _ vrefl_rect)
 (at level 0, format "[ 'new' 'Type'  'for'  v ]") : form_scope.

Notation "[ 'newType' 'for' v 'by' rec ]" := (NewType v _ rec vrefl)
 (at level 0, format "[ 'newType'  'for'  v  'by'  rec ]") : form_scope.

Definition innew T nT x := @Sub T predT nT x (erefl true).
Arguments innew [T nT].
Prenex Implicits innew.

Lemma innew_val T nT : cancel val (@innew T nT).
Proof. by move=> u; apply: val_inj; apply: SubK. Qed.

(* Prenex Implicits and renaming. *)
Notation sval := (@proj1_sig _ _).
Notation "@ 'sval'" := (@proj1_sig) (at level 10, format "@ 'sval'").

Section SubEqType.

Variables (T : eqType) (P : pred T) (sT : subType P).

Local Notation ev_ax := (fun T v => @Equality.axiom T (fun x y => v x == v y)).
Lemma val_eqP : ev_ax sT val. Proof. exact: inj_eqAxiom val_inj. Qed.

Definition sub_eqMixin := EqMixin val_eqP.
Canonical sub_eqType := Eval hnf in EqType sT sub_eqMixin.

Definition SubEqMixin :=
  (let: SubType _ v _ _ _ as sT' := sT
     return ev_ax sT' val -> Equality.class_of sT' in
   fun vP : ev_ax _ v => EqMixin vP
   ) val_eqP.

Lemma val_eqE (u v : sT) : (val u == val v) = (u == v).
Proof. by []. Qed.

End SubEqType.

Arguments val_eqP [T P sT x y].
Prenex Implicits val_eqP.

Notation "[ 'eqMixin' 'of' T 'by' <: ]" := (SubEqMixin _ : Equality.class_of T)
  (at level 0, format "[ 'eqMixin'  'of'  T  'by'  <: ]") : form_scope.

(* ssrnat ---------------------------------------------------------- *)

Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : Equality.axiom eqn.
Proof.
move=> n m; apply: (iffP idP) => [|<-]; last by elim n.
by elim: n m => [|n IHn] [|m] //= /IHn->.
Qed.

Canonical nat_eqMixin := EqMixin eqnP.
Canonical nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Arguments eqnP [x y].
Prenex Implicits eqnP.

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.

Lemma oddb (b : bool) : odd b = b. Proof. by case: b. Qed.

Definition subn_rec := minus.
Notation "m - n" := (subn_rec m n) : nat_rec_scope.

Definition subn := nosimpl subn_rec.
Notation "m - n" := (subn m n) : nat_scope.

Definition leq m n := m - n == 0.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n"  := (m.+1 <= n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n"  := (n < m) (only parsing)  : nat_scope.


Notation "m <= n <= p" := ((m <= n) && (n <= p)) : nat_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : nat_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : nat_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : nat_scope.

Open Scope nat_scope.


Lemma ltnS m n : (m < n.+1) = (m <= n). Proof. by []. Qed.
Lemma leq0n n : 0 <= n.                 Proof. by []. Qed.
Lemma ltn0Sn n : 0 < n.+1.              Proof. by []. Qed.
Lemma ltn0 n : n < 0 = false.           Proof. by []. Qed.
Lemma leqnn n : n <= n.                 Proof. by elim: n. Qed.
Hint Resolve leqnn.
Lemma leqnSn n : n <= n.+1.             Proof. by elim: n. Qed.

Lemma leq_trans n m p : m <= n -> n <= p -> m <= p.
Admitted.
Lemma leq_ltn_trans n m p : m <= n -> n < p -> m < p.
Admitted.
Lemma leqW m n : m <= n -> m <= n.+1.
Admitted.
Hint Resolve leqnSn.
Lemma ltnW m n : m < n -> m <= n.
Proof. exact: leq_trans. Qed.
Hint Resolve ltnW.

Definition addn_rec := plus.
Notation "m + n" := (addn_rec m n) : nat_rec_scope.

Definition addn := nosimpl addn_rec.
Notation "m + n" := (addn m n) : nat_scope.

Lemma addn0 : right_id 0 addn. Proof. by move=> n; apply/eqP; elim: n. Qed.
Lemma add0n : left_id 0 addn.            Proof. by []. Qed.
Lemma addSn m n : m.+1 + n = (m + n).+1. Proof. by []. Qed.
Lemma addnS m n : m + n.+1 = (m + n).+1. Proof. by elim: m. Qed.

Lemma addnCA : left_commutative addn.
Proof. by move=> m n p; elim: m => //= m; rewrite addnS => <-. Qed.

Lemma addnC : commutative addn.
Proof. by move=> m n; rewrite -{1}[n]addn0 addnCA addn0. Qed.

Lemma addnA : associative addn.
Proof. by move=> m n p; rewrite (addnC n) addnCA addnC. Qed.

Lemma subnK m n : m <= n -> (n - m) + m = n.
Admitted.


Definition muln_rec := mult.
Notation "m * n" := (muln_rec m n) : nat_rec_scope.

Definition muln := nosimpl muln_rec.
Notation "m * n" := (muln m n) : nat_scope.

Lemma mul0n : left_zero 0 muln.          Proof. by []. Qed.
Lemma muln0 : right_zero 0 muln.         Proof. by elim. Qed.
Lemma mul1n : left_id 1 muln.            Proof. exact: addn0. Qed.

Lemma mulSn m n : m.+1 * n = n + m * n.  Proof. by []. Qed.
Lemma mulSnr m n : m.+1 * n = m * n + n. Proof. exact: addnC. Qed.

Lemma mulnS m n : m * n.+1 = m + m * n.
Proof. by elim: m => // m; rewrite !mulSn !addSn addnCA => ->. Qed.

Lemma mulnSr m n : m * n.+1 = m * n + m.
Proof. by rewrite addnC mulnS. Qed.

Lemma muln1 : right_id 1 muln.
Proof. by move=> n; rewrite mulnSr muln0. Qed.

Lemma mulnC : commutative muln.
Proof.
by move=> m n; elim: m => [|m]; rewrite (muln0, mulnS) // mulSn => ->.
Qed.

Lemma mulnDl : left_distributive muln addn.
Proof. by move=> m1 m2 n; elim: m1 => //= m1 IHm; rewrite -addnA -IHm. Qed.

Lemma mulnDr : right_distributive muln addn.
Proof. by move=> m n1 n2; rewrite !(mulnC m) mulnDl. Qed.

Lemma mulnA : associative muln.
Proof. by move=> m n p; elim: m => //= m; rewrite mulSn mulnDl => ->. Qed.

Lemma mulnCA : left_commutative muln.
Proof. by move=> m n1 n2; rewrite !mulnA (mulnC m). Qed.

Lemma mulnAC : right_commutative muln.
Proof. by move=> m n p; rewrite -!mulnA (mulnC n). Qed.

Lemma mulnACA : interchange muln muln.
Proof. by move=> m n p q; rewrite -!mulnA (mulnCA n). Qed.

(* seq ------------------------------------------------------------- *)

Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

(* Inductive seq (T : Type) : Type := Nil | Cons of T & seq T. *)
Notation seq := list.
Prenex Implicits cons.
Notation Cons T := (@cons T) (only parsing).
Notation Nil T := (@nil T) (only parsing).

Bind Scope seq_scope with list.
Arguments cons _%type _ _%SEQ.

(* As :: and ++ are (improperly) declared in Init.datatypes, we only rebind   *)
(* them here.                                                                 *)
Infix "::" := cons : seq_scope.

(* GG - this triggers a camlp4 warning, as if this Notation had been Reserved *)
Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::])
  (at level 0, format "[ ::  x1 ]") : seq_scope.

Notation "[ :: x & s ]" := (x :: s) (at level 0, only parsing) : seq_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (x1 :: x2 :: .. (xn :: s) ..)
  (at level 0, format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Section Sequences.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type s : seq T.

Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.

Fixpoint cat s1 s2 := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

Lemma cat0s s : [::] ++ s = s. Proof. by []. Qed.

Lemma cats0 s : s ++ [::] = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma catA s1 s2 s3 : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof. by elim: s1 => //= x s1 ->. Qed.

Fixpoint nth s n {struct n} :=
  if s is x :: s' then if n is n'.+1 then @nth s' n' else x else x0.

Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].

CoInductive last_spec : seq T -> Type :=
  | LastNil        : last_spec [::]
  | LastRcons s x  : last_spec (rcons s x).

Lemma lastP s : last_spec s.
Proof using. Admitted.

Lemma last_ind P :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof using. Admitted.


Section Map.

Variables (T2 : Type) (f : T -> T2).

Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

End Map.

Section SeqFind.

Variable a : pred T.

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

End SeqFind.

End Sequences.

Infix "++" := cat : seq_scope.

Notation count_mem x := (count (pred_of_simpl (pred1 x))).

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Local Notation nth := (nth x0).
Implicit Type s : seq T.
Implicit Types x y z : T.

Fixpoint eqseq s1 s2 {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : Equality.axiom eqseq.
Proof.
move; elim=> [|x1 s1 IHs] [|x2 s2]; do [by constructor | simpl].
case: (x1 =P x2) => [<-|neqx]; last by right; case.
by apply: (iffP (IHs s2)) => [<-|[]].
Qed.

Canonical seq_eqMixin := EqMixin eqseqP.
Canonical seq_eqType := Eval hnf in EqType (seq T) seq_eqMixin.

Fixpoint mem_seq (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

Definition eqseq_class := seq T.
Identity Coercion seq_of_eqseq : eqseq_class >-> seq.
Coercion pred_of_eq_seq (s : eqseq_class) : pred_class := [eta mem_seq s].

Canonical seq_predType := @mkPredType T (seq T) pred_of_eq_seq.

Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.

End EqSeq.

Definition bitseq := seq bool.
Canonical bitseq_eqType := Eval hnf in [eqType of bitseq].
Canonical bitseq_predType := Eval hnf in [predType of bitseq].

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then let r := pmap s' in oapp (cons^~ r) r (f x) else [::].

End Pmap.

Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].

Section FoldRight.

Variables (T : Type) (R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Lemma mem_iota m n i : (i \in iota m n) = (m <= i) && (i < m + n).
Admitted.


(* choice ------------------------------------------------------------- *)

Module Choice.

Section ClassDef.

Record mixin_of T := Mixin {
  find : pred T -> nat -> option T;
  _ : forall P n x, find P n = Some x -> P x;
  _ : forall P : pred T, (exists x, P x) -> exists n, find P n;
  _ : forall P Q : pred T, P =1 Q -> find P =1 find Q
}.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation choiceType := type.
Notation choiceMixin := mixin_of.
Notation ChoiceType T m := (@pack T m _ _ id).
Notation "[ 'choiceType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'choiceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'choiceType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'choiceType'  'of'  T ]") : form_scope.

End Exports.

End Choice.
Export Choice.Exports.

Section ChoiceTheory.

Variable T : choiceType.

Section CanChoice.

Variables (sT : Type) (f : sT -> T).

Lemma PcanChoiceMixin f' : pcancel f f' -> choiceMixin sT.
Admitted.

Definition CanChoiceMixin f' (fK : cancel f f') :=
  PcanChoiceMixin (can_pcan fK).

End CanChoice.

Section SubChoice.

Variables (P : pred T) (sT : subType P).

Definition sub_choiceMixin := PcanChoiceMixin (@valK T P sT).
Definition sub_choiceClass := @Choice.Class sT (sub_eqMixin sT) sub_choiceMixin.
Canonical sub_choiceType := Choice.Pack sub_choiceClass sT.

End SubChoice.


Fact seq_choiceMixin : choiceMixin (seq T).
Admitted.
Canonical seq_choiceType := Eval hnf in ChoiceType (seq T) seq_choiceMixin.
End ChoiceTheory.

Fact nat_choiceMixin : choiceMixin nat.
Proof.
pose f := [fun (P : pred nat) n => if P n then Some n else None].
exists f => [P n m | P [n Pn] | P Q eqPQ n] /=; last by rewrite eqPQ.
  by case: ifP => // Pn [<-].
by exists n; rewrite Pn.
Qed.
Canonical nat_choiceType := Eval hnf in ChoiceType nat nat_choiceMixin.

Definition bool_choiceMixin := CanChoiceMixin oddb.
Canonical bool_choiceType := Eval hnf in ChoiceType bool bool_choiceMixin.
Canonical bitseq_choiceType := Eval hnf in [choiceType of bitseq].


Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
  (sub_choiceMixin _ : choiceMixin T)
  (at level 0, format "[ 'choiceMixin'  'of'  T  'by'  <: ]") : form_scope.




Module Countable.

Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.

Definition EqMixin T m := PcanEqMixin (@pickleK T m).
Definition ChoiceMixin T m := PcanChoiceMixin (@pickleK T m).

Section ClassDef.

Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation countType := type.
Notation CountType T m := (@pack T m _ _ id).
Notation CountMixin := Mixin.
Notation CountChoiceMixin := ChoiceMixin.
Notation "[ 'countType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
 (at level 0, format "[ 'countType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'countType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'countType'  'of'  T ]") : form_scope.

End Exports.

End Countable.
Export Countable.Exports.

Definition unpickle T := Countable.unpickle (Countable.class T).
Definition pickle T := Countable.pickle (Countable.class T).
Arguments unpickle [T].
Prenex Implicits pickle unpickle.

Section CountableTheory.

Variable T : countType.

Lemma pickleK : @pcancel nat T pickle unpickle.
Proof. exact: Countable.pickleK. Qed.

Definition pickle_inv n :=
  obind (fun x : T => if pickle x == n then Some x else None) (unpickle n).

Lemma pickle_invK : ocancel pickle_inv pickle.
Proof.
by rewrite /pickle_inv => n; case def_x: (unpickle n) => //= [x]; case: eqP.
Qed.

Lemma pickleK_inv : pcancel pickle pickle_inv.
Proof. by rewrite /pickle_inv => x; rewrite pickleK /= eqxx. Qed.

Lemma pcan_pickleK sT f f' :
  @pcancel T sT f f' -> pcancel (pickle \o f) (pcomp f' unpickle).
Proof. by move=> fK x; rewrite /pcomp pickleK /= fK. Qed.

Definition PcanCountMixin sT f f' (fK : pcancel f f') :=
  @CountMixin sT _ _ (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

Definition sub_countMixin P sT := PcanCountMixin (@valK T P sT).

End CountableTheory.
Notation "[ 'countMixin' 'of' T 'by' <: ]" :=
    (sub_countMixin _ : Countable.mixin_of T)
  (at level 0, format "[ 'countMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SubCountType.

Variables (T : choiceType) (P : pred T).
Import Countable.

Structure subCountType : Type :=
  SubCountType {subCount_sort :> subType P; _ : mixin_of subCount_sort}.

Coercion sub_countType (sT : subCountType) :=
  Eval hnf in pack (let: SubCountType _ m := sT return mixin_of sT in m) id.
Canonical sub_countType.

Definition pack_subCountType U :=
  fun sT cT & sub_sort sT * sort cT -> U * U =>
  fun b m   & phant_id (Class b m) (class cT) => @SubCountType sT m.

End SubCountType.

(* This assumes that T has both countType and subType structures. *)
Notation "[ 'subCountType' 'of' T ]" :=
    (@pack_subCountType _ _ T _ _ id _ _ id)
  (at level 0, format "[ 'subCountType'  'of'  T ]") : form_scope.

Lemma nat_pickleK : pcancel id (@Some nat). Proof. by []. Qed.
Definition nat_countMixin := CountMixin nat_pickleK.
Canonical nat_countType := Eval hnf in CountType nat nat_countMixin.

(* fintype --------------------------------------------------------- *)

Module Finite.

Section RawMixin.

Variable T : eqType.

Definition axiom e := forall x : T, count_mem x e = 1.

Lemma uniq_enumP e : uniq e -> e =i T -> axiom e.
Admitted.

Record mixin_of := Mixin {
  mixin_base : Countable.mixin_of T;
  mixin_enum : seq T;
  _ : axiom mixin_enum
}.

End RawMixin.

Section Mixins.

Variable T : countType.

Definition EnumMixin :=
  let: Countable.Pack _ (Countable.Class _ m) _ as cT := T
    return forall e : seq cT, axiom e -> mixin_of cT in
  @Mixin (EqType _ _) m.

Definition UniqMixin e Ue eT := @EnumMixin e (uniq_enumP Ue eT).

Variable n : nat.

End Mixins.

Section ClassDef.

Record class_of T := Class {
  base : Choice.class_of T;
  mixin : mixin_of (Equality.Pack base T)
}.
Definition base2 T c := Countable.Class (@base T c) (mixin_base (mixin c)).
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (EqType T b0)) :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (base2 xclass) xT.

End ClassDef.

Module Import Exports.
Coercion mixin_base : mixin_of >-> Countable.mixin_of.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion base2 : class_of >-> Countable.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Notation finType := type.
Notation FinType T m := (@pack T _ m _ _ id _ id).
Notation FinMixin := EnumMixin.
Notation UniqFinMixin := UniqMixin.
Notation "[ 'finType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'finType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'finType'  'of'  T ]") : form_scope.
End Exports.

Module Type EnumSig.
Parameter enum : forall cT : type, seq cT.
Axiom enumDef : enum = fun cT => mixin_enum (class cT).
End EnumSig.

Module EnumDef : EnumSig.
Definition enum cT := mixin_enum (class cT).
Definition enumDef := erefl enum.
End EnumDef.

Notation enum := EnumDef.enum.

End Finite.
Export Finite.Exports.

Section SubFinType.

Variables (T : choiceType) (P : pred T).
Import Finite.

Structure subFinType := SubFinType {
  subFin_sort :> subType P;
  _ : mixin_of (sub_eqType subFin_sort)
}.

Definition pack_subFinType U :=
  fun cT b m & phant_id (class cT) (@Class U b m) =>
  fun sT m'  & phant_id m' m => @SubFinType sT m'.

Implicit Type sT : subFinType.

Definition subFin_mixin sT :=
  let: SubFinType _ m := sT return mixin_of (sub_eqType sT) in m.

Coercion subFinType_subCountType sT := @SubCountType _ _ sT (subFin_mixin sT).
Canonical subFinType_subCountType.

Coercion subFinType_finType sT :=
  Pack (@Class sT (sub_choiceClass sT) (subFin_mixin sT)) sT.
Canonical subFinType_finType.

Definition enum_mem T (mA : mem_pred _) := filter mA (Finite.enum T).
Definition image_mem T T' f mA : seq T' := map f (@enum_mem T mA).
Definition codom T T' f := @image_mem T T' f (mem T).

Lemma codom_val sT x : (x \in codom (val : sT -> T)) = P x.
Admitted.

End SubFinType.


(* This assumes that T has both finType and subCountType structures. *)
Notation "[ 'subFinType' 'of' T ]" := (@pack_subFinType _ _ T _ _ _ id _ _ id)
  (at level 0, format "[ 'subFinType'  'of'  T ]") : form_scope.



Section OrdinalSub.

Variable n : nat.

Inductive ordinal : predArgType := Ordinal m of m < n.

Coercion nat_of_ord i := let: Ordinal m _ := i in m.

Canonical ordinal_subType := [subType for nat_of_ord].
Definition ordinal_eqMixin := Eval hnf in [eqMixin of ordinal by <:].
Canonical ordinal_eqType := Eval hnf in EqType ordinal ordinal_eqMixin.
Definition ordinal_choiceMixin := [choiceMixin of ordinal by <:].
Canonical ordinal_choiceType :=
  Eval hnf in ChoiceType ordinal ordinal_choiceMixin.
Definition ordinal_countMixin := [countMixin of ordinal by <:].
Canonical ordinal_countType := Eval hnf in CountType ordinal ordinal_countMixin.
Canonical ordinal_subCountType := [subCountType of ordinal].

Lemma ltn_ord (i : ordinal) : i < n. Proof. exact: valP i. Qed.

Lemma ord_inj : injective nat_of_ord. Proof. exact: val_inj. Qed.

Definition ord_enum : seq ordinal := pmap insub (iota 0 n).

Lemma val_ord_enum : map val ord_enum = iota 0 n.
Admitted.

Lemma ord_enum_uniq : uniq ord_enum.
Admitted.

Lemma mem_ord_enum i : i \in ord_enum.
Admitted.

Definition ordinal_finMixin :=
  Eval hnf in UniqFinMixin ord_enum_uniq mem_ord_enum.
Canonical ordinal_finType := Eval hnf in FinType ordinal ordinal_finMixin.
Canonical ordinal_subFinType := Eval hnf in [subFinType of ordinal].

End OrdinalSub.

Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").

(* bigop ----------------------------------------------------------------- *)

Reserved Notation "\big [ op / idx ]_ i F"
  (at level 36, F at level 36, op, idx at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / idx ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A ) '/  '  F ']'").

Module Monoid.

Section Definitions.
Variables (T : Type) (idm : T).

Structure law := Law {
  operator : T -> T -> T;
  _ : associative operator;
  _ : left_id idm operator;
  _ : right_id idm operator
}.
Local Coercion operator : law >-> Funclass.

Structure com_law := ComLaw {
   com_operator : law;
   _ : commutative com_operator
}.
Local Coercion com_operator : com_law >-> law.

Structure mul_law := MulLaw {
  mul_operator : T -> T -> T;
  _ : left_zero idm mul_operator;
  _ : right_zero idm mul_operator
}.
Local Coercion mul_operator : mul_law >-> Funclass.

Structure add_law (mul : T -> T -> T) := AddLaw {
  add_operator : com_law;
  _ : left_distributive mul add_operator;
  _ : right_distributive mul add_operator
}.
Local Coercion add_operator : add_law >-> com_law.

Let op_id (op1 op2 : T -> T -> T) := phant_id op1 op2.

Definition clone_law op :=
  fun (opL : law) & op_id opL op =>
  fun opmA op1m opm1 (opL' := @Law op opmA op1m opm1)
    & phant_id opL' opL => opL'.

Definition clone_com_law op :=
  fun (opL : law) (opC : com_law) & op_id opL op & op_id opC op =>
  fun opmC (opC' := @ComLaw opL opmC) & phant_id opC' opC => opC'.

Definition clone_mul_law op :=
  fun (opM : mul_law) & op_id opM op =>
  fun op0m opm0 (opM' := @MulLaw op op0m opm0) & phant_id opM' opM => opM'.

Definition clone_add_law mop aop :=
  fun (opC : com_law) (opA : add_law mop) & op_id opC aop & op_id opA aop =>
  fun mopDm mopmD (opA' := @AddLaw mop opC mopDm mopmD)
    & phant_id opA' opA => opA'.

End Definitions.

Module Import Exports.
Coercion operator : law >-> Funclass.
Coercion com_operator : com_law >-> law.
Coercion mul_operator : mul_law >-> Funclass.
Coercion add_operator : add_law >-> com_law.
Notation "[ 'law' 'of' f ]" := (@clone_law _ _ f _ id _ _ _ id)
  (at level 0, format"[ 'law'  'of'  f ]") : form_scope.
Notation "[ 'com_law' 'of' f ]" := (@clone_com_law _ _ f _ _ id id _ id)
  (at level 0, format "[ 'com_law'  'of'  f ]") : form_scope.
Notation "[ 'mul_law' 'of' f ]" := (@clone_mul_law _ _ f _ id _ _ id)
  (at level 0, format"[ 'mul_law'  'of'  f ]") : form_scope.
Notation "[ 'add_law' m 'of' a ]" := (@clone_add_law _ _ m a _ _ id id _ _ id)
  (at level 0, format "[ 'add_law'  m  'of'  a ]") : form_scope.
End Exports.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T) (inv : T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof. by move=> mul1x x; rewrite mulC. Qed.

Lemma mulC_zero : left_zero zero mul -> right_zero zero mul.
Proof. by move=> mul0x x; rewrite mulC. Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof. by move=> mul_addl x y z; rewrite !(mulC x). Qed.

End CommutativeAxioms.
Module Theory.

Section Theory.
Variables (T : Type) (idm : T).

Section Plain.
Variable mul : law idm.
Lemma mul1m : left_id idm mul. Proof. by case mul. Qed.
Lemma mulm1 : right_id idm mul. Proof. by case mul. Qed.
Lemma mulmA : associative mul. Proof. by case mul. Qed.
(*Lemma iteropE n x : iterop n mul x idm = iter n (mul x) idm.*)

End Plain.

Section Commutative.
Variable mul : com_law idm.
Lemma mulmC : commutative mul. Proof. by case mul. Qed.
Lemma mulmCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulmA (mulmC x). Qed.
Lemma mulmAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulmA (mulmC y). Qed.
Lemma mulmACA : interchange mul mul.
Proof. by move=> x y z t; rewrite -!mulmA (mulmCA y). Qed.
End Commutative.

Section Mul.
Variable mul : mul_law idm.
Lemma mul0m : left_zero idm mul. Proof. by case mul. Qed.
Lemma mulm0 : right_zero idm mul. Proof. by case mul. Qed.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Lemma addmA : associative add. Proof. exact: mulmA. Qed.
Lemma addmC : commutative add. Proof. exact: mulmC. Qed.
Lemma addmCA : left_commutative add. Proof. exact: mulmCA. Qed.
Lemma addmAC : right_commutative add. Proof. exact: mulmAC. Qed.
Lemma add0m : left_id idm add. Proof. exact: mul1m. Qed.
Lemma addm0 : right_id idm add. Proof. exact: mulm1. Qed.
Lemma mulm_addl : left_distributive mul add. Proof. by case add. Qed.
Lemma mulm_addr : right_distributive mul add. Proof. by case add. Qed.
End Add.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Theory.

End Theory.
Include Theory.

End Monoid.
Export Monoid.Exports.

Section PervasiveMonoids.

Import Monoid.

Canonical andb_monoid := Law andbA andTb andbT.
Canonical andb_comoid := ComLaw andbC.

Canonical andb_muloid := MulLaw andFb andbF.
Canonical orb_monoid := Law orbA orFb orbF.
Canonical orb_comoid := ComLaw orbC.
Canonical orb_muloid := MulLaw orTb orbT.
Canonical addb_monoid := Law addbA addFb addbF.
Canonical addb_comoid := ComLaw addbC.
Canonical orb_addoid := AddLaw andb_orl andb_orr.
Canonical andb_addoid := AddLaw orb_andl orb_andr.
Canonical addb_addoid := AddLaw andb_addl andb_addr.

Canonical addn_monoid := Law addnA add0n addn0.
Canonical addn_comoid := ComLaw addnC.
Canonical muln_monoid := Law mulnA mul1n muln1.
Canonical muln_comoid := ComLaw mulnC.
Canonical muln_muloid := MulLaw mul0n muln0.
Canonical addn_addoid := AddLaw mulnDl mulnDr.

Canonical cat_monoid T := Law (@catA T) (@cat0s T) (@cats0 T).

End PervasiveMonoids.
Delimit Scope big_scope with BIG.
Open Scope big_scope.

(* The bigbody wrapper is a workaround for a quirk of the Coq pretty-printer, *)
(* which would fail to redisplay the \big notation when the <general_term> or *)
(* <condition> do not depend on the bound index. The BigBody constructor      *)
(* packages both in in a term in which i occurs; it also depends on the       *)
(* iterated <op>, as this can give more information on the expected type of   *)
(* the <general_term>, thus allowing for the insertion of coercions.          *)
CoInductive bigbody R I := BigBody of I & (R -> R -> R) & bool & R.

Definition applybig {R I} (body : bigbody R I) x :=
  let: BigBody _ op b v := body in if b then op v x else x.

Definition reducebig R I idx r (body : I -> bigbody R I) :=
  foldr (applybig \o body) idx r.

Module Type BigOpSig.
Parameter bigop : forall R I, R -> seq I -> (I -> bigbody R I) -> R.
Axiom bigopE : bigop = reducebig.
End BigOpSig.

Module BigOp : BigOpSig.
Definition bigop := reducebig.
Lemma bigopE : bigop = reducebig. Proof. by []. Qed.
End BigOp.

Notation bigop := BigOp.bigop (only parsing).
Canonical bigop_unlock := Unlockable BigOp.bigopE.

Definition index_iota m n := iota m (n - m).

Definition index_enum (T : finType) := Finite.enum T.

Lemma mem_index_iota m n i : i \in index_iota m n = (m <= i < n).
Admitted.

Lemma mem_index_enum T i : i \in index_enum T.
Admitted.

Hint Resolve mem_index_enum.

(*
Lemma filter_index_enum T P : filter P (index_enum T) = enum P.
Proof. by []. Qed.
*)

Notation "\big [ op / idx ]_ ( i <- r | P ) F" :=
  (bigop idx r (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r ) F" :=
  (bigop idx r (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op P%B F))
     : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op true F))
     : big_scope.
Notation "\big [ op / idx ]_ ( i | P ) F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ i F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op P%B F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i : t ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op true F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i < n | P ) F" :=
  (\big[op/idx]_(i : ordinal n | P%B) F) : big_scope.
Notation "\big [ op / idx ]_ ( i < n ) F" :=
  (\big[op/idx]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A | P ) F" :=
  (\big[op/idx]_(i | (i \in A) && P) F) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A ) F" :=
  (\big[op/idx]_(i | i \in A) F) : big_scope.

Notation BIG_F := (F in \big[_/_]_(i <- _ | _) F i)%pattern.
Notation BIG_P := (P in \big[_/_]_(i <- _ | P i) _)%pattern.

(* Induction loading *)
Lemma big_load R (K K' : R -> Type) idx op I r (P : pred I) F :
  K (\big[op/idx]_(i <- r | P i) F i) * K' (\big[op/idx]_(i <- r | P i) F i)
  -> K' (\big[op/idx]_(i <- r | P i) F i).
Proof. by case. Qed.

Arguments big_load [R] K [K'] idx op [I].

Section Elim3.

Variables (R1 R2 R3 : Type) (K : R1 -> R2 -> R3 -> Type).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).
Variables (id3 : R3) (op3 : R3 -> R3 -> R3).

Hypothesis Kid : K id1 id2 id3.

Lemma big_rec3 I r (P : pred I) F1 F2 F3
    (K_F : forall i y1 y2 y3, P i -> K y1 y2 y3 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2) (op3 (F3 i) y3)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F. Qed.

Hypothesis Kop : forall x1 x2 x3 y1 y2 y3,
  K x1 x2 x3 -> K y1 y2 y3-> K (op1 x1 y1) (op2 x2 y2) (op3 x3 y3).
Lemma big_ind3 I r (P : pred I) F1 F2 F3
   (K_F : forall i, P i -> K (F1 i) (F2 i) (F3 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i).
Proof. by apply: big_rec3 => i x1 x2 x3 /K_F; apply: Kop. Qed.

End Elim3.

Arguments big_rec3 [R1 R2 R3] K [id1 op1 id2 op2 id3 op3] _ [I r P F1 F2 F3].
Arguments big_ind3 [R1 R2 R3] K [id1 op1 id2 op2 id3 op3] _ _ [I r P F1 F2 F3].

Section Elim2.

Variables (R1 R2 : Type) (K : R1 -> R2 -> Type) (f : R2 -> R1).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).

Hypothesis Kid : K id1 id2.

Lemma big_rec2 I r (P : pred I) F1 F2
    (K_F : forall i y1 y2, P i -> K y1 y2 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i) (\big[op2/id2]_(i <- r | P i) F2 i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F. Qed.

Hypothesis Kop : forall x1 x2 y1 y2,
  K x1 x2 -> K y1 y2 -> K (op1 x1 y1) (op2 x2 y2).
Lemma big_ind2 I r (P : pred I) F1 F2 (K_F : forall i, P i -> K (F1 i) (F2 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i) (\big[op2/id2]_(i <- r | P i) F2 i).
Proof. by apply: big_rec2 => i x1 x2 /K_F; apply: Kop. Qed.

Hypotheses (f_op : {morph f : x y / op2 x y >-> op1 x y}) (f_id : f id2 = id1).
Lemma big_morph I r (P : pred I) F :
  f (\big[op2/id2]_(i <- r | P i) F i) = \big[op1/id1]_(i <- r | P i) f (F i).
Proof. by rewrite unlock; elim: r => //= i r <-; rewrite -f_op -fun_if. Qed.

End Elim2.

Arguments big_rec2 [R1 R2] K [id1 op1 id2 op2] _ [I r P F1 F2].
Arguments big_ind2 [R1 R2] K [id1 op1 id2 op2] _ _ [I r P F1 F2].
Arguments big_morph [R1 R2] f [id1 op1 id2 op2] _ _ [I].

Section Elim1.

Variables (R : Type) (K : R -> Type) (f : R -> R).
Variables (idx : R) (op op' : R -> R -> R).

Hypothesis Kid : K idx.

Lemma big_rec I r (P : pred I) F
    (Kop : forall i x, P i -> K x -> K (op (F i) x)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: Kop. Qed.

Hypothesis Kop : forall x y, K x -> K y -> K (op x y).
Lemma big_ind I r (P : pred I) F (K_F : forall i, P i -> K (F i)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof. by apply: big_rec => // i x /K_F /Kop; apply. Qed.

Hypothesis Kop' : forall x y, K x -> K y -> op x y = op' x y.
Lemma eq_big_op I r (P : pred I) F (K_F : forall i, P i -> K (F i)) :
  \big[op/idx]_(i <- r | P i) F i = \big[op'/idx]_(i <- r | P i) F i.
Proof.
by elim/(big_load K): _; elim/big_rec2: _ => // i _ y Pi [Ky <-]; auto.
Qed.

Hypotheses (fM : {morph f : x y / op x y}) (f_id : f idx = idx).
Lemma big_endo I r (P : pred I) F :
  f (\big[op/idx]_(i <- r | P i) F i) = \big[op/idx]_(i <- r | P i) f (F i).
Proof. exact: big_morph. Qed.

End Elim1.

Arguments big_rec [R] K [idx op] _ [I r P F].
Arguments big_ind [R] K [idx op] _ _ [I r P F].
Arguments eq_big_op [R] K [idx op] op' _ _ _ [I].
Arguments big_endo [R] f [idx op] _ _ [I].

(* zmodp -------------------------------------------------------------------- *)

Lemma ord1 : all_equal_to (@Ordinal 1 0 is_true_true : 'I_1).
Admitted.
