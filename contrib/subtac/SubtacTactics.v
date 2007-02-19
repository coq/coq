Ltac induction_with_subterm c H :=
  let x := fresh "x" in
  let y := fresh "y" in
  (set(x := c) ; assert(y:x = c) by reflexivity ;
  rewrite <- y in H ; 
  induction H ; subst).

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
 | [H : (ex _) |- _] => destruct H
 | [H : (ex2 _) |- _] => destruct H
 | [H : (sig _) |- _] => destruct H
 | [H : (_ /\ _) |- _] => destruct H
end.

Ltac destruct_exists := repeat (destruct_one_pair) .

(* Destructs calls to f in hypothesis or conclusion, useful if f creates a subset object *)
Ltac destruct_call f :=
  match goal with
    | H : ?T |- _  =>
      match T with
         context [f ?x ?y ?z] => destruct (f x y z)
       | context [f ?x ?y] => destruct (f x y)
       | context [f ?x] => destruct (f x)        
      end
    | |- ?T  =>
      match T with
        context [f ?x ?y ?z] => let n := fresh "H" in set (n:=f x y z); destruct n
        | context [f ?x ?y] => let n := fresh "H" in set (n:=f x y); destruct n
        | context [f ?x] => let n := fresh "H" in set (n:=f x); destruct n
      end
    end.

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
