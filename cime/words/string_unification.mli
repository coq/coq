(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


(* Computes the solutions of [l1 w1 = w2 l2] with [w1] and [w2] not empty *)

val superpose :
  ('symbol Words.word * 'symbol Words.word) 
  -> ('symbol Words.word * 'symbol Words.word) 
    -> ('symbol Words.word * 'symbol Words.word) list


val unify :
  'symbol Words.word -> 'symbol Words.word ->  
    (('symbol Words.word * 'symbol Words.word) * ('symbol Words.word * 'symbol Words.word)) list 
