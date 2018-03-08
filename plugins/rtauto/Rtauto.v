(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


Require Export List.
Require Export Bintree.
Require Import Bool BinPos.

Declare ML Module "rtauto_plugin".

Ltac clean:=try (simpl;congruence).

Inductive form:Set:=
  Atom : positive -> form
| Arrow : form -> form -> form
| Bot
| Conjunct : form -> form -> form
| Disjunct : form -> form -> form.

Notation "[ n ]":=(Atom n).
Notation "A =>> B":= (Arrow A B) (at level 59, right associativity).
Notation "#" := Bot.
Notation "A //\\ B" := (Conjunct A B) (at level 57, left associativity).
Notation "A \\// B" := (Disjunct A B) (at level 58, left associativity).

Definition ctx := Store form.

Fixpoint pos_eq (m n:positive) {struct m} :bool :=
match m with
  xI mm => match n with xI nn => pos_eq mm nn | _ => false end
| xO mm => match n with xO nn => pos_eq mm nn | _ => false end
| xH => match n with xH => true | _ => false end
end.

Theorem pos_eq_refl : forall m n, pos_eq m n = true -> m = n.
induction m;simpl;destruct n;congruence ||
(intro e;apply f_equal;auto).
Qed.

Fixpoint form_eq (p q:form) {struct p} :bool :=
match p with
  Atom m => match q with Atom n => pos_eq m n | _ => false end
| Arrow p1 p2 =>
match q with
  Arrow q1 q2 => form_eq p1 q1 && form_eq p2 q2
| _ => false end
| Bot => match q with Bot => true | _ => false end
| Conjunct p1 p2 =>
match q with
  Conjunct q1 q2 => form_eq p1 q1 && form_eq p2 q2
| _ => false
end
| Disjunct p1 p2 =>
match q with
  Disjunct q1 q2 => form_eq p1 q1 && form_eq p2 q2
| _ => false
end
end.

Theorem form_eq_refl: forall p q, form_eq p q = true -> p = q.
induction p;destruct q;simpl;clean.
intro h;generalize (pos_eq_refl _ _ h);congruence.
case_eq (form_eq p1 q1);clean.
intros e1 e2;generalize (IHp1 _ e1) (IHp2 _ e2);congruence.
case_eq (form_eq p1 q1);clean.
intros e1 e2;generalize (IHp1 _ e1) (IHp2 _ e2);congruence.
case_eq (form_eq p1 q1);clean.
intros e1 e2;generalize (IHp1 _ e1) (IHp2 _ e2);congruence.
Qed.

Arguments form_eq_refl [p q] _.

Section with_env.

Variable env:Store Prop.

Fixpoint interp_form (f:form): Prop :=
match f with
[n]=> match get n env with PNone => True | PSome P => P end
| A =>> B => (interp_form A) -> (interp_form B)
| # => False
| A //\\ B => (interp_form A) /\ (interp_form B)
| A \\// B => (interp_form A) \/ (interp_form B)
end.

Notation "[[ A ]]" := (interp_form A).

Fixpoint interp_ctx (hyps:ctx) (F:Full hyps) (G:Prop) {struct F} : Prop :=
match F with
  F_empty => G
| F_push H hyps0 F0 =>  interp_ctx hyps0 F0  ([[H]] -> G)
end.

Ltac wipe := intros;simpl;constructor.

Lemma compose0 :
forall hyps F (A:Prop),
 A ->
 (interp_ctx hyps F A).
induction F;intros A H;simpl;auto.
Qed.

Lemma compose1 :
forall hyps F (A B:Prop),
 (A -> B) ->
 (interp_ctx hyps F A) ->
 (interp_ctx hyps F B).
induction F;intros A B H;simpl;auto.
apply IHF;auto.
Qed.

Theorem compose2 :
forall hyps F (A B C:Prop),
 (A -> B -> C) ->
 (interp_ctx hyps F A) ->
 (interp_ctx hyps F B) ->
 (interp_ctx hyps F C).
induction F;intros A B C H;simpl;auto.
apply IHF;auto.
Qed.

Theorem compose3 :
forall hyps F (A B C D:Prop),
 (A -> B -> C -> D) ->
 (interp_ctx hyps F A) ->
 (interp_ctx hyps F B) ->
 (interp_ctx hyps F C) ->
 (interp_ctx hyps F D).
induction F;intros A B C D H;simpl;auto.
apply IHF;auto.
Qed.

Lemma weaken : forall hyps F f G,
 (interp_ctx hyps F G) ->
 (interp_ctx (hyps\f)  (F_push f hyps F) G).
induction F;simpl;intros;auto.
apply compose1 with ([[a]]-> G);auto.
Qed.

Theorem project_In : forall hyps F g,
In g hyps F ->
interp_ctx hyps F [[g]].
induction F;simpl.
contradiction.
intros g H;destruct H.
subst;apply compose0;simpl;trivial.
apply compose1 with [[g]];auto.
Qed.

Theorem project : forall hyps F p g,
get  p hyps = PSome g->
interp_ctx hyps F [[g]].
intros hyps F p g e; apply project_In.
apply get_In with p;assumption.
Qed.

Arguments project [hyps] F [p g] _.

Inductive proof:Set :=
  Ax : positive -> proof
| I_Arrow : proof -> proof
| E_Arrow : positive -> positive -> proof -> proof
| D_Arrow : positive -> proof -> proof -> proof
| E_False : positive -> proof
| I_And: proof -> proof -> proof
| E_And: positive -> proof -> proof
| D_And: positive -> proof -> proof
| I_Or_l: proof -> proof
| I_Or_r: proof -> proof
| E_Or: positive -> proof -> proof -> proof
| D_Or: positive -> proof -> proof
| Cut: form -> proof -> proof -> proof.

Notation "hyps \ A" := (push A hyps) (at level 72,left associativity).

Fixpoint check_proof (hyps:ctx) (gl:form) (P:proof) {struct P}: bool :=
 match P with
   Ax i =>
     match get i hyps with
         PSome F => form_eq F gl
 | _ => false
    end
| I_Arrow p =>
   match gl with
      A  =>> B  => check_proof (hyps \ A) B p
   | _ => false
    end
| E_Arrow i j p =>
   match get i hyps,get j hyps with
       PSome A,PSome (B =>>C) =>
         form_eq A B && check_proof (hyps \ C) (gl) p
    | _,_ => false
    end
| D_Arrow i p1 p2 =>
   match get i hyps with
      PSome  ((A =>>B)=>>C) =>
     (check_proof ( hyps \ B =>> C \ A) B p1) && (check_proof (hyps \ C) gl p2)
    | _ => false
  end
| E_False i =>
  match get i hyps with
    PSome # => true
  | _ => false
  end
| I_And p1 p2 =>
   match gl with
      A //\\ B =>
      check_proof hyps A p1 && check_proof hyps B p2
      | _ => false
      end
| E_And i p =>
   match get i hyps with
      PSome  (A //\\ B) => check_proof (hyps \ A \ B) gl p
    | _=> false
   end
| D_And i p =>
   match get i hyps with
      PSome  (A //\\ B =>> C) => check_proof (hyps \ A=>>B=>>C) gl p
    | _=> false
   end
| I_Or_l p =>
   match gl with
      (A \\// B) => check_proof hyps A p
      | _ => false
      end
| I_Or_r p =>
   match gl with
      (A \\// B) => check_proof hyps B p
      | _ => false
      end
| E_Or i p1 p2 =>
  match get i hyps with
  PSome (A \\// B) =>
  check_proof (hyps \ A) gl p1 && check_proof (hyps \ B) gl p2
  | _=> false
  end
| D_Or i p =>
   match get i hyps with
      PSome  (A \\// B =>> C) =>
      (check_proof (hyps \ A=>>C \ B=>>C) gl p)
    | _=> false
   end
| Cut A p1 p2 =>
  check_proof hyps A p1 && check_proof (hyps \ A) gl p2
end.

Theorem interp_proof:
forall p hyps F gl,
check_proof hyps gl p = true -> interp_ctx hyps F [[gl]].

induction p; intros hyps F gl.

- (* Axiom *)
  simpl;case_eq (get p hyps);clean.
  intros f nth_f e;rewrite <- (form_eq_refl e).
  apply project with p;trivial.

- (* Arrow_Intro *)
  destruct gl; clean.
  simpl; intros.
  change (interp_ctx (hyps\gl1)  (F_push gl1 hyps F) [[gl2]]).
  apply IHp; try constructor; trivial.

- (* Arrow_Elim *)
  simpl check_proof; case_eq (get p hyps); clean.
  intros f ef; case_eq (get p0 hyps); clean.
  intros f0 ef0; destruct f0; clean.
  case_eq (form_eq f f0_1); clean.
  simpl; intros e check_p1.
  generalize  (project  F ef) (project  F ef0)
              (IHp (hyps \ f0_2) (F_push f0_2 hyps F) gl check_p1);
    clear check_p1 IHp p p0 p1 ef ef0.
  simpl.
  apply compose3.
  rewrite (form_eq_refl e).
  auto.

- (* Arrow_Destruct *)
  simpl; case_eq (get p1 hyps); clean.
  intros f ef; destruct f; clean.
  destruct f1; clean.
  case_eq (check_proof (hyps \ f1_2 =>> f2 \ f1_1) f1_2 p2); clean.
  intros check_p1 check_p2.
  generalize (project F ef)
             (IHp1 (hyps \ f1_2 =>> f2 \ f1_1)
                   (F_push f1_1 (hyps \ f1_2 =>> f2)
                           (F_push (f1_2 =>> f2) hyps F)) f1_2 check_p1)
             (IHp2 (hyps \ f2) (F_push f2 hyps F) gl check_p2).
  simpl; apply compose3; auto.

- (* False_Elim *)
  simpl; case_eq (get p hyps); clean.
  intros f ef; destruct f; clean.
  intros _; generalize (project F ef).
  apply compose1; apply False_ind.

- (* And_Intro *)
  simpl; destruct gl; clean.
  case_eq (check_proof hyps gl1 p1); clean.
  intros Hp1 Hp2;generalize (IHp1 hyps F gl1 Hp1) (IHp2 hyps F gl2 Hp2).
  apply compose2 ; simpl; auto.

- (* And_Elim *)
  simpl; case_eq (get p hyps); clean.
  intros f ef; destruct f; clean.
  intro check_p;
    generalize  (project F ef)
                (IHp (hyps \ f1 \ f2) (F_push f2 (hyps \ f1) (F_push f1 hyps F)) gl check_p).
  simpl; apply compose2; intros [h1 h2]; auto.

- (* And_Destruct*)
  simpl; case_eq (get p hyps); clean.
  intros f ef; destruct f; clean.
  destruct f1; clean.
  intro H;
    generalize (project F ef)
               (IHp (hyps \ f1_1 =>> f1_2 =>> f2)
                    (F_push (f1_1 =>> f1_2 =>> f2) hyps F) gl H);
    clear H; simpl.
  apply compose2; auto.

- (* Or_Intro_left *)
  destruct gl; clean.
  intro Hp; generalize (IHp hyps F gl1 Hp).
  apply compose1; simpl; auto.

- (* Or_Intro_right *)
  destruct gl; clean.
  intro Hp; generalize (IHp hyps F gl2 Hp).
  apply compose1; simpl; auto.

- (* Or_elim *)
  simpl; case_eq (get p1 hyps); clean.
  intros f ef; destruct f; clean.
  case_eq (check_proof (hyps \ f1) gl p2); clean.
  intros check_p1 check_p2;
    generalize (project F ef)
               (IHp1 (hyps \ f1) (F_push f1 hyps F) gl check_p1)
               (IHp2 (hyps \ f2) (F_push f2 hyps F) gl check_p2);
    simpl; apply compose3; simpl; intro h; destruct h; auto.

- (* Or_Destruct *)
  simpl; case_eq (get p hyps); clean.
  intros f ef; destruct f; clean.
  destruct f1; clean.
  intro check_p0;
    generalize (project F ef)
               (IHp (hyps \ f1_1 =>> f2 \ f1_2 =>> f2)
                    (F_push (f1_2 =>> f2) (hyps \ f1_1 =>> f2)
                            (F_push (f1_1 =>> f2) hyps F)) gl check_p0);
    simpl.
  apply compose2; auto.

- (* Cut *)
  simpl; case_eq (check_proof hyps f p1); clean.
  intros check_p1 check_p2;
    generalize (IHp1 hyps F f check_p1)
               (IHp2 (hyps\f) (F_push f hyps F) gl check_p2);
    simpl; apply compose2; auto.
Qed.

Theorem Reflect: forall gl prf, if check_proof empty gl prf then [[gl]] else True.
intros gl prf;case_eq (check_proof empty gl prf);intro check_prf.
change (interp_ctx empty F_empty [[gl]]) ;
apply interp_proof with prf;assumption.
trivial.
Qed.

End with_env.

(*
(* A small example *)
Parameters A B C D:Prop.
Theorem toto:A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
exact (Reflect (empty \ A \ B \ C)
([1] //\\ ([2] \\// [3]) =>> [1] //\\ [2] \\// [1] //\\ [3])
(I_Arrow (E_And 1 (E_Or 3
  (I_Or_l (I_And (Ax 2) (Ax 4)))
  (I_Or_r (I_And (Ax 2) (Ax 4))))))).
Qed.
Print toto.
*)
