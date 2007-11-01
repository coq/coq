
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)


(**********************************************************************
       Tactic.v                                                                                    
          Useful tactics                                                                       
 **********************************************************************)

(**************************************
  A simple tactic to end a proof 
**************************************)
Ltac  finish := intros; auto; trivial; discriminate.


(**************************************
 A tactic for proof by contradiction
     with contradict H 
         H: ~A |-   B      gives           |-   A
         H: ~A |- ~ B     gives  H: B |-   A
         H:   A |-   B      gives           |- ~ A
         H:   A |-   B      gives           |- ~ A
         H:   A |- ~ B     gives  H: A |- ~ A
**************************************)

Ltac  contradict name := 
     let term := type of name in (
     match term with 
       (~_) => 
          match goal with 
            |- ~ _  => let x := fresh in
                     (intros x; case name; 
                      generalize x; clear x name;
                      intro name)
          | |- _    => case name; clear name
          end
     | _ => 
          match goal with 
            |- ~ _  => let x := fresh in
                    (intros x;  absurd term;
                       [idtac | exact name]; generalize x; clear x name;
                       intros name)
          | |- _    => generalize name; absurd term;
                       [idtac | exact name]; clear name
          end
     end).


(**************************************
 A tactic to use f_equal? theorems 
**************************************)

Ltac eq_tac := 
 match goal with
       |-  (?g _ = ?g _) => apply f_equal with (f := g)
 |     |-  (?g ?X _ = ?g  ?X _) => apply f_equal with (f := g  X)
 |     |-  (?g _ _ = ?g  _ _) => apply f_equal2 with (f := g)
 |     |-  (?g ?X ?Y _ = ?g ?X ?Y _) => apply f_equal with (f := g X Y)
 |     |-  (?g ?X _ _ = ?g ?X _ _) => apply f_equal2 with (f := g X)
 |     |-  (?g _ _ _ = ?g _ _ _) => apply f_equal3 with (f := g)
 |     |-  (?g ?X ?Y ?Z _ = ?g ?X ?Y ?Z _) => apply f_equal with (f := g X Y Z)
 |     |-  (?g ?X ?Y _ _ = ?g ?X ?Y _ _) => apply f_equal2 with (f := g X Y)
 |     |-  (?g ?X _ _ _ = ?g ?X _ _ _) => apply f_equal3 with (f := g X)
 |     |-  (?g _ _ _ _ _ = ?g _ _ _ _) => apply f_equal4 with (f := g)
 end.

(************************************** 
 A stupid tactic that tries auto also after applying sym_equal
**************************************)

Ltac sauto := (intros; apply sym_equal; auto; fail) || auto.
