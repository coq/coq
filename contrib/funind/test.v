(* Declare ML Module "csimpl" "tacinvutils" "tacinv-new". *)
Require Import Arith.
(* Require Export Tacinvnew. *)
 
Fixpoint trivfun [n : nat] : nat :=
 Cases n of O => O | (S m) => (trivfun m) end.
(*Parameter P: nat -> Prop.
  Goal  (n:nat)(P n).
  Intro n.
  Invfunproof trivfun params n.
  Show Proof.
*)

(* essaie de parametre variables non locaux:*) 

Variables varessai:nat.
Goal(trivfun varessai) = O.
Functional Induction trivfun varessai.
Trivial.
Simpl.
Assumption.
Defined.
 

Functional Scheme triv_ind := Induction for trivfun.

Lemma bisrepetita:(n' : nat)  (trivfun n') = O.
Intros n'.
Functional Induction trivfun n'.
Trivial.
Simpl.
Assumption.
Save.


Fixpoint iseven [n : nat] : bool :=
 Cases n of O => true | (S (S m)) => (iseven m) | _ => false end.
 
Fixpoint funex [n : nat] : nat :=
 Cases (iseven n) of
   true => n
  | false =>
      Cases n of O => O | (S r) => (funex r) end
 end.
(*Goal (n:nat) (funex n) = O -> (iseven n)=true.
  Intro n.
  Invfunproof funex params n.
  Show Proof.
   *)
 
Fixpoint nat_equal_bool [n : nat] : nat ->  bool :=
 [m : nat]  Cases n of
              O =>
                Cases m of O => true | _ => false end
             | (S p) =>
                 Cases m of O => false | (S q) => (nat_equal_bool p q) end
            end.
Require Export Arith.
Require Export Div2.
 
Lemma div2_inf: (n : nat)  (le (div2 n) n).
Intros n.
(Functional Induction div2 n).
Auto with arith.
Auto with arith.

Simpl.
Apply le_S.
Apply le_n_S.
Exact H.
Qed.
(* 
  Functional Scheme plus_ind := Induction plus.
  Print plus_ind.
   *)
 
Fixpoint essai [x : nat] : nat * nat ->  nat :=
 [p : nat * nat]  ( Case p of [n, m : ?]  Cases n of
                                            O => O
                                           | (S q) =>
                                               Cases x of
                                                 O => (S O)
                                                | (S r) => (S (essai r (q, m)))
                                               end
                                          end end ).
 
Lemma essai_essai:
 (x : nat)
 (p : nat * nat)  ( Case p of [n, m : ?] (lt O n) ->  (lt O (essai x p)) end ).
Intros x p.
(Functional Induction essai x p); Intros.
Inversion H.
Simpl; Try Abstract ( Auto with arith ).
Simpl; Try Abstract ( Auto with arith ).
Qed.
(* 
  Lemma dep_dep:(x:nat)(le x (S x)).
  Intro x.
  Invfunproof essai_essai_trans params x.
   
   
  Fixpoint  essaidep[x:nat]: () :=
  [p:nat*nat]
  let (n,m)=p in
  Cases n of
   | O => O
   |(S q) =>  
  Cases x of
  | O => (S O)
  | (S r) => (S (essai r (q,m)))
  end
  end.
   *)
 
Fixpoint plus_x_not_five' [n : nat] : nat ->  nat :=
 [m : nat]  Cases n of
              O => O
             | (S q) =>
                 Cases m of
                   O => (S (plus_x_not_five' q O))
                  | (S r) => (S (plus_x_not_five' q (S r)))
                 end
            end.
 
Lemma notplusfive':
 (x, y : nat) y = (S (S (S (S (S O))))) ->  (plus_x_not_five' x y) = x.
Intros x y.
(Functional Induction plus_x_not_five' x y); Intros hyp.
Auto.
Inversion hyp.
Intros.
Simpl.
Auto.
Qed.
 
Fixpoint plus_x_not_five [n : nat] : nat ->  nat :=
 [m : nat]
  Cases n of
    O => O
   | (S q) =>
       Cases (nat_equal_bool m (S q)) of   true => (S (plus_x_not_five q m))
                                          | false => (S (plus_x_not_five q m))
       end
  end.
 
Lemma notplusfive:
 (x, y : nat) y = (S (S (S (S (S O))))) ->  (plus_x_not_five x y) = x.
Intros x y.
Unfold plus_x_not_five.
(Functional Induction plus_x_not_five x y) ; Simpl; Intros hyp;
 Fold plus_x_not_five.
Auto.
Auto.
Auto.
Qed.
 
Fixpoint plus_x_not_five'' [n : nat] : nat ->  nat :=
 [m : nat]  let x = (nat_equal_bool m (S (S (S (S (S O)))))) in
              let y = O in
                Cases n of
                  O => y
                 | (S q) =>
                     let recapp = (plus_x_not_five'' q m) in
                       Cases x of true => (S recapp) | false => (S recapp) end
                end.
(* let in pas encore traites *)
 
Lemma notplusfive'':
 (x, y : nat) y = (S (S (S (S (S O))))) ->  (plus_x_not_five'' x y) = x.
Intros a b.
Unfold plus_x_not_five''.
(Functional Induction plus_x_not_five'' a b); Intros hyp; Simpl; Auto.
Qed.
 
Lemma iseq_eq: (n, m : nat) n = m ->  (nat_equal_bool n m) = true.
Intros n m.
Unfold nat_equal_bool.
(Functional Induction nat_equal_bool n m); Simpl; Intros hyp; Auto.
Inversion hyp.
Inversion hyp.
Qed.
 
Lemma iseq_eq': (n, m : nat) (nat_equal_bool n m) = true ->  n = m.
Intros n m.
Unfold nat_equal_bool.
(Functional Induction nat_equal_bool n m); Simpl; Intros eg; Auto.
Inversion eg.
Inversion eg.
Qed.
 
Definition iszero : nat ->  bool :=
   [n : nat]  Cases n of O => true | _ => false end.
 
Inductive istrue : bool ->  Prop :=
  istrue0: (istrue true) .
 
Lemma toto: (n : nat) n = O ->  (istrue (iszero n)).
Intros x.
(Functional Induction iszero x); Intros eg; Simpl.
Apply istrue0.
Inversion eg.
Qed.
(* 
  plus = 
  Fix plus
  {plus [n:nat] : nat->nat :=
     [m:nat]Cases n of
              O => m
            | (S p) => (S (plus p m))
            end}
     : nat->nat->nat
   *)
 
Lemma inf_x_plusxy': (x, y : nat)  (le x (plus x y)).
Intros n m.
(Functional Induction plus n m); Intros.
Auto with arith.
Auto with arith.
Qed.
(* *****essais *)
 
Lemma inf_x_plusxy'': (x : nat)  (le x (plus x O)).
Intros n.
Unfold plus.
(Functional Induction plus n O); Intros.
Auto with arith.
Apply le_n_S.
Assumption.
Qed.
 
Lemma inf_x_plusxy''': (x : nat)  (le x (plus O x)).
Intros n.
(Functional Induction plus O n); Intros;Auto with arith.
Qed.

(*Lemma inf_x_plusxy''':(x,y:nat)(le x (plus (S x) (S y))).
  Intros n m.
  Invfunproof plus params (S n) (S m);Intros.
  Auto with arith.
  Assumption.
  Save.*)
 
Fixpoint mod2 [n : nat] : nat :=
 Cases n of   O => O
             | (S (S m)) => (S (mod2 m))
             | _ => O end.
 
Lemma princ_mod2: (n : nat)  (le (mod2 n) n).
Intros n.
(Functional Induction mod2 n); Simpl; Auto with arith.
Qed.
 
Definition isfour : nat ->  bool :=
   [n : nat]  Cases n of (S (S (S (S O)))) => true | _ => false end.
 
Definition isononeorfour : nat ->  bool :=
   [n : nat]  Cases n of   (S O) => true
                          | (S (S (S (S O)))) => true
                          | _ => false end.
(* Inductive istrue : bool -> Prop := istrue0 : (istrue true). *)
 
Lemma toto'': (n : nat) (istrue (isfour n)) ->  (istrue (isononeorfour n)).
Intros n.
(Functional Induction isononeorfour n); Intros istr; Simpl; Inversion istr.
Apply istrue0.
Qed.
 
Lemma toto': (n, m : nat) n = (S (S (S (S O)))) ->  (istrue (isononeorfour n)).
Intros n.
(Functional Induction isononeorfour n); Intros m istr; Inversion istr.
Apply istrue0.
Qed.
 
Definition ftest : nat -> nat ->  nat :=
   [n, m : nat]  Cases n of
                   O =>
                     Cases m of O => O | _ => (S O) end
                  | (S p) => O
                 end.
 
Lemma test1: (n, m : nat)  (le (ftest n m) (S (S O))).
Intros n m.
(Functional Induction ftest n m); Auto with arith.
Qed.
 
Lemma test11: (m : nat)  (le (ftest O m) (S (S O))).
Intros m.
(Functional Induction ftest O m).
Auto with arith.
Auto with arith.
Qed.
 
Definition ftest4 : nat -> nat ->  nat :=
   [n, m : nat]  Cases n of
                   O =>
                     Cases m of O => O | (S q) => (S O) end
                  | (S p) =>
                      Cases m of O => O | (S r) => (S O) end
                 end.
 
Lemma test4: (n, m : nat)  (le (ftest n m) (S (S O))).
Intros n m.
(Functional Induction ftest n m); Auto with arith.
Qed.
 
Lemma test4': (n, m : nat)  (le (ftest4 (S n) m) (S (S O))).
Intros n m.
(Functional Induction ftest4 (S n) m).
Auto with arith.
Auto with arith.
Qed.
 
Definition ftest44 : nat * nat -> nat -> nat ->  nat :=
   [x : nat * nat]
   [n, m : nat]
    ( Case x of [p, q : ?]  Cases n of
                              O =>
                                Cases m of O => O | (S q) => (S O) end
                             | (S p) =>
                                 Cases m of O => O | (S r) => (S O) end
                            end end ).
 
Lemma test44:
 (pq : nat * nat) (n, m, o, r, s : nat)  (le (ftest44 pq n (S m)) (S (S O))).
Intros pq n m o r s.
(Functional Induction ftest44 pq n (S m)).
Auto with arith.
Auto with arith.
Auto with arith.
Auto with arith.
Qed.
 
Fixpoint ftest2 [n : nat] : nat ->  nat :=
 [m : nat]  Cases n of
              O =>
                Cases m of O => O | (S q) => O end
             | (S p) => (ftest2 p m)
            end.
 
Lemma test2: (n, m : nat)  (le (ftest2 n m) (S (S O))).
Intros n m.
(Functional Induction ftest2 n m) ; Simpl; Intros; Auto.
Qed.
 
Fixpoint ftest3 [n : nat] : nat ->  nat :=
 [m : nat]  Cases n of
              O => O
             | (S p) =>
                 Cases m of O => (ftest3 p O) | (S r) => O end
            end.
 
Lemma test3: (n, m : nat)  (le (ftest3 n m) (S (S O))).
Intros n m.
(Functional Induction ftest3 n m).
Intros.
Auto.
Intros.
Auto.
Intros.
Simpl.
Auto.
Qed.
 
Fixpoint ftest5 [n : nat] : nat ->  nat :=
 [m : nat]  Cases n of
              O => O
             | (S p) =>
                 Cases m of O => (ftest5 p O) | (S r) => (ftest5 p r) end
            end.
 
Lemma test5: (n, m : nat)  (le (ftest5 n m) (S (S O))).
Intros n m.
(Functional Induction ftest5 n m).
Intros.
Auto.
Intros.
Auto.
Intros.
Simpl.
Auto.
Qed.
 
Definition ftest7 : (n : nat)  nat :=
   [n : nat]  Cases (ftest5 n O) of O => O | (S r) => O end.
 
Lemma essai7:
 (Hrec : (n : nat) (ftest5 n O) = O ->  (le (ftest7 n) (S (S O))))
 (Hrec0 : (n, r : nat) (ftest5 n O) = (S r) ->  (le (ftest7 n) (S (S O))))
 (n : nat)  (le (ftest7 n) (S (S O))).
Intros hyp1 hyp2 n.
Unfold ftest7.
(Functional Induction ftest7 n); Auto.
Qed.
 
Fixpoint ftest6 [n : nat] : nat ->  nat :=
 [m : nat]
  Cases n of
    O => O
   | (S p) =>
       Cases (ftest5 p O) of O => (ftest6 p O) | (S r) => (ftest6 p r) end
  end.

 
Lemma princ6:
 ((n, m : nat) n = O ->  (le (ftest6 O m) (S (S O)))) ->
 ((n, m, p : nat)
  (le (ftest6 p O) (S (S O))) ->
  (ftest5 p O) = O -> n = (S p) ->  (le (ftest6 (S p) m) (S (S O)))) ->
 ((n, m, p, r : nat)
  (le (ftest6 p r) (S (S O))) ->
  (ftest5 p O) = (S r) -> n = (S p) ->  (le (ftest6 (S p) m) (S (S O)))) ->
 (x, y : nat)  (le (ftest6 x y) (S (S O))).
Intros hyp1 hyp2 hyp3 n m.
Generalize hyp1 hyp2 hyp3.
Clear hyp1 hyp2 hyp3.
(Functional Induction ftest6 n m);Auto.
Qed.
 
Lemma essai6: (n, m : nat)  (le (ftest6 n m) (S (S O))).
Intros n m.
Unfold ftest6.
(Functional Induction ftest6 n m); Simpl; Auto.
Qed.
  (* 
   Local Variables: 
   coq-prog-name: "../mytop.out  -I . -emacs"
   compile-command: "make -C <chemin du makefile> <chemin du makefile au fichier>.vo"
   End:
*)
