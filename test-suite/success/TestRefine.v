(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Petit bench vite fait, mal fait *)

Require Refine.


(************************************************************************)

Lemma essai : (x:nat)x=x.

Refine (([x0:nat]Cases x0 of
    O => ?
  | (S p) => ?
  end) :: (x:nat)x=x).  (* x0=x0 et x0=x0 *)

Restart.

Refine [x0:nat]<[n:nat]n=n>Case x0 of ? [p:nat]? end. (* OK *)

Restart.

Refine [x0:nat]<[n:nat]n=n>Cases x0 of O => ? | (S p) => ? end. (* OK *)

Restart.

(**
Refine [x0:nat]Cases x0 of O => ? | (S p) => ? end. (* cannot be executed *)
**)

Abort.


(************************************************************************)

Lemma T : nat. 

Refine (S ?).

Abort.


(************************************************************************)

Lemma essai2 : (x:nat)x=x.

Refine Fix f{f/1 : (x:nat)x=x := [x:nat]? }.

Restart.

Refine Fix f{f/1 : (x:nat)x=x :=
  [x:nat]<[n:nat](eq nat n n)>Case x of ? [p:nat]? end}.

Restart.

Refine Fix f{f/1 : (x:nat)x=x :=
  [x:nat]<[n:nat]n=n>Cases x of O => ? | (S p) => ? end}.

Restart.

Refine Fix f{f/1 : (x:nat)x=x :=
  [x:nat]<[n:nat](eq nat n n)>Case x of
       ?
       [p:nat](f_equal nat nat S p p ?) end}.

Restart.

Refine Fix f{f/1 : (x:nat)x=x :=
  [x:nat]<[n:nat](eq nat n n)>Cases x of
       O => ?
     | (S p) =>(f_equal nat nat S p p ?) end}.

Abort.


(************************************************************************)

Lemma essai : nat.

Parameter f : nat*nat -> nat -> nat. 

Refine (f ? ([x:nat](? :: nat) O)).

Restart.

Refine (f ? O).

Abort.


(************************************************************************)

Parameter P : nat -> Prop.

Lemma essai : { x:nat | x=(S O) }.

Refine (exist nat ? (S O) ?).  (* ECHEC *)

Restart.

(* mais si on contraint par le but alors ca marche : *)
(* Remarque : on peut toujours faire ça *)
Refine ((exist nat ? (S O) ?) :: { x:nat | x=(S O) }).

Restart.

Refine (exist nat [x:nat](x=(S O)) (S O) ?).

Abort.


(************************************************************************)

Lemma essai : (n:nat){ x:nat | x=(S n) }.

Refine [n:nat]<[n:nat]{x:nat|x=(S n)}>Case n of ? [p:nat]? end.

Restart.

Refine (([n:nat]Case n of ? [p:nat]? end) :: (n:nat){ x:nat | x=(S n) }).

Restart.

Refine [n:nat]<[n:nat]{x:nat|x=(S n)}>Cases n of O => ? | (S p) => ? end.

Restart.

Refine Fix f{f/1 :(n:nat){x:nat|x=(S n)} :=
        [n:nat]<[n:nat]{x:nat|x=(S n)}>Case n of ? [p:nat]? end}.

Restart.

Refine Fix f{f/1 :(n:nat){x:nat|x=(S n)} :=
        [n:nat]<[n:nat]{x:nat|x=(S n)}>Cases n of O => ? | (S p) => ? end}.

Exists (S O). Trivial. 
Elim (f0 p).
Refine [x:nat][h:x=(S p)](exist nat [x:nat]x=(S (S p)) (S x) ?). 
Rewrite h. Auto.
Save.



(* Quelques essais de recurrence bien fondée *)

Require Wf.
Require Wf_nat.

Lemma essai_wf : nat->nat.

Refine [x:nat](well_founded_induction
      	       nat
      	       lt ?
               [_:nat]nat->nat
	       [phi0:nat][w:(phi:nat)(lt phi phi0)->nat->nat](w x ?)
	       x x).
Exact lt_wf.

Abort.


Require Compare_dec.
Require Lt.

Lemma fibo : nat -> nat.
Refine (well_founded_induction
       nat
       lt ?
       [_:nat]nat
       [x0:nat][fib:(x:nat)(lt x x0)->nat]
         Cases (zerop x0) of 
      	   (left _)   => (S O)
      	 | (right h1) => Cases (zerop (pred x0)) of
      	                   (left _)   => (S O)
                         | (right h2) => (plus (fib (pred x0) ?)
      	       	       	       	       	       (fib (pred (pred x0)) ?))
		     end
	 end).
Exact lt_wf.
Auto with arith.
Apply lt_trans with m:=(pred x0); Auto with arith.
Save.


