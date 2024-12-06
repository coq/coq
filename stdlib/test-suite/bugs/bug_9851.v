From Stdlib Require Import Ring_base.
Record word : Type := Build_word
  { rep : Type;
    zero : rep; one: rep;
    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;
    opp : rep -> rep;
    mul : rep -> rep -> rep;
    }.
Axiom rth
     : forall (word : word ),
       @ring_theory (@rep word)
         (@zero word)
         (@one word) (@add word)
         (@mul word) (@sub word)
         (@opp word) (@eq (@rep word)).

Fail Add Ring wring: (@rth _).
