Ltac induction_with_subterm c H :=
  let x := fresh "x" in
  let y := fresh "y" in
  (remember c as x ; rewrite <- y in H ; induction H ; subst).

Ltac induction_on_subterm c :=
  let x := fresh "x" in
  let y := fresh "y" in
  (set(x := c) ; assert(y:x = c) by reflexivity ; clearbody x ; induction x ; inversion y ; try subst ; 
  clear y).

Ltac induction_with_subterms c c' H :=
  let x := fresh "x" in
  let y := fresh "y" in
  let z := fresh "z" in
  let w := fresh "w" in
  (set(x := c) ; assert(y:x = c) by reflexivity ;
  set(z := c') ; assert(w:z = c') by reflexivity ;
  rewrite <- y in H ; rewrite <- w in H ; 
  induction H ; subst).


Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

Ltac destruct_pairs := repeat (destruct_one_pair).

Ltac destruct_one_ex :=
  let tac H := let ph := fresh "H" in destruct H as [H ph] in
    match goal with
      | [H : (ex _) |- _] => tac H
      | [H : (sig ?P) |- _ ] => tac H
      | [H : (ex2 _) |- _] => tac H
    end.

Ltac destruct_exists := repeat (destruct_one_ex).

Tactic Notation "destruct" "exist" ident(t) ident(Ht) := destruct t as [t Ht].

Tactic Notation "destruct" "or" ident(H) := destruct H as [H|H].

Tactic Notation "contradiction" "by" constr(t) := 
  let H := fresh in assert t as H by auto with * ; contradiction.

Ltac discriminates :=
  match goal with
    | [ H : ?x <> ?x |- _ ] => elim H ; reflexivity
    | _ => discriminate
  end.

Ltac destruct_conjs := repeat (destruct_one_pair || destruct_one_ex).

Ltac on_last_hyp tac := 
  match goal with
    [ H : _ |- _ ] => tac H
  end.

Tactic Notation "on_last_hyp" tactic(t) := on_last_hyp t.

Ltac revert_last := 
  match goal with
    [ H : _ |- _ ] => revert H
  end.

Ltac reverse := repeat revert_last.

Ltac on_call f tac :=
  match goal with
    | H : ?T |- _  =>
      match T with
        | context [f ?x ?y ?z ?w ?v ?u] => tac (f x y z w v u)
        | context [f ?x ?y ?z ?w ?v] => tac (f x y z w v)
        | context [f ?x ?y ?z ?w] => tac (f x y z w)
        | context [f ?x ?y ?z] => tac (f x y z)
        | context [f ?x ?y] => tac (f x y) 
        | context [f ?x] => tac (f x)
      end
    | |- ?T  =>
      match T with
        | context [f ?x ?y ?z ?w ?v ?u] => tac (f x y z w v u)
        | context [f ?x ?y ?z ?w ?v] => tac (f x y z w v)
        | context [f ?x ?y ?z ?w] => tac (f x y z w)
        | context [f ?x ?y ?z] => tac (f x y z)
        | context [f ?x ?y] => tac (f x y)
        | context [f ?x] => tac (f x)
      end
  end.

(* Destructs calls to f in hypothesis or conclusion, useful if f creates a subset object *)
Ltac destruct_call f :=
  let tac t := destruct t in on_call f tac.

Ltac destruct_call_as f l :=
  let tac t := destruct t as l in on_call f tac.

Tactic Notation "destruct_call" constr(f) := destruct_call f.
Tactic Notation "destruct_call" constr(f) "as" simple_intropattern(l) := destruct_call_as f l.

Ltac myinjection :=
  let tac H := inversion H ; subst ; clear H in
    match goal with
      | [ H : ?f ?a = ?f' ?a' |- _ ] => tac H
      | [ H : ?f ?a ?b = ?f' ?a' ?b'  |- _ ] => tac H
      | [ H : ?f ?a ?b ?c = ?f' ?a' ?b' ?c' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d= ?f' ?a' ?b' ?c' ?d' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e= ?f' ?a' ?b' ?c' ?d' ?e' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g= ?f' ?a' ?b' ?c' ?d' ?e' ?g'  |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g ?h= ?f' ?a' ?b' ?c' ?d' ?e'?g' ?h' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g ?h ?i = ?f' ?a' ?b' ?c' ?d' ?e'?g' ?h' ?i' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g ?h ?i ?j = ?f' ?a' ?b' ?c' ?d' ?e'?g' ?h' ?i' ?j' |- _ ] => tac H
      | _ => idtac
    end.

Ltac destruct_nondep H := let H0 := fresh "H" in assert(H0 := H); destruct H0.

Ltac bang :=
  match goal with
    | |- ?x => 
      match x with
        | context [False_rect _ ?p] => elim p
      end
  end.

Require Import Eqdep.

Ltac elim_eq_rect :=
  match goal with
    | [ |- ?t ] => 
      match t with
        | context [ @eq_rect _ _ _ _ _ ?p ] => 
          let P := fresh "P" in 
            set (P := p); simpl in P ; 
	      try ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
        | context [ @eq_rect _ _ _ _ _ ?p _ ] => 
          let P := fresh "P" in 
            set (P := p); simpl in P ; 
	      try ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
      end
  end.

Ltac real_elim_eq_rect :=
  match goal with
    | [ |- ?t ] => 
      match t with
        | context [ @eq_rect _ _ _ _ _ ?p ] => 
          let P := fresh "P" in 
            set (P := p); simpl in P ; 
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
        | context [ @eq_rect _ _ _ _ _ ?p _ ] => 
          let P := fresh "P" in 
            set (P := p); simpl in P ; 
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
      end
  end.
 