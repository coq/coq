Require CC.


Theorem t1: (A:Set)(a:A)(f:A->A)
	(f a)=a->(f (f a))=a.
Intros.
CC.
Save.

Theorem t2: (A:Set)(a,b:A)(f:A->A)(g:A->A->A)
	a=(f a)->(g b (f a))=(f (f a))->(g a b)=(f (g b a))->
	(g a b)=a.
Intros.
CC.
Save.

(* 15=0 /\ 10=0 /\ 6=0 -> 0=1 *)

Theorem t3: (N:Set)(o:N)(s:N->N)(d:N->N)
	(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s o)))))))))))))))=o->
	(s (s (s (s (s (s (s (s (s (s o))))))))))=o->
	(s (s (s (s (s (s o))))))=o->
	o=(s o).
Intros.
CC.
Save.

(* Examples that fail due to dependencies *) 

(* yields transitivity problem *)

Theorem dep:(A:Set)(P:A->Set)(f,g:(x:A)(P x))(x,y:A)
    (e:x=y)(e0:(f y)=(g y))(f x)=(g x).
Intros;Dependent Rewrite -> e;Exact e0.
Save.

(* yields congruence problem *)

Theorem dep2:(A,B:Set)(f:(A:Set)(b:bool)if b then unit else A->unit)(e:A==B)
   (f A true)=(f B true).
Intros;Rewrite e;Reflexivity.
Save.

(* example with CCSolve *)

Theorem t4 :  (A:Set; P:(A->Prop); u,v:A)u=v->(P u)->(P v).
Intros.
CCsolve.
Save.
