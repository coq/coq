Require Export Int31.
Require Import NMake.
Require Import ZnZ.

Open Scope int31_scope.

Definition int31_op : znz_op int31.
 split.

 (* Conversion functions with Z *)
 exact (31%positive). (* number of digits *)
 exact (31). (* number of digits *)
 exact (phi). (* conversion to Z *)
 exact (positive_to_int31). (* positive -> N*int31 :  p => N,i where p = N*2^31+phi i *)
 exact head031.  (* number of head 0 *)
 exact tail031.  (* number of tail 0 *)

 (* Basic constructors *)
 exact 0. (* 0 *)
 exact 1. (* 1 *)
 exact Tn. (* 2^31 - 1 *)
 (* A function which given two int31 i and j, returns a double word
    which is worth i*2^31+j *)
 exact (fun i j => match (match i ?= 0 with | Eq =>  j ?= 0 | not0 => not0 end) with | Eq => W0 | _ => WW i j end).
 (* two special cases where i and j are respectively taken equal to 0 *)
 exact (fun i => match i ?= 0 with | Eq => W0 | _ => WW i 0 end).
 exact (fun j => match j ?= 0 with | Eq => W0 | _ => WW 0 j end).

 (* Comparison *)
 exact compare31.
 exact (fun i => match i ?= 0 with | Eq => true | _ => false end).

 (* Basic arithmetic operations *)
 (* opposite functions *)
 exact (fun i => 0 -c i).
 exact (fun i => 0 - i).
 exact (fun i => 0-i-1). (* the carry is always -1*)
 (* successor and addition functions *)
 exact (fun i => i +c 1).
 exact add31c.
 exact add31carryc.
 exact (fun i => i + 1).
 exact add31.
 exact (fun i j => i + j + 1).
 (* predecessor and subtraction functions *)
 exact (fun i => i -c 1).
 exact sub31c.
 exact sub31carryc.
 exact (fun i => i - 1).
 exact sub31.
 exact (fun i j => i - j - 1).
 (* multiplication functions *)
 exact mul31c.
 exact mul31.
 exact (fun x => x *c x).

 (* special (euclidian) division operations *)
 exact div3121.
 exact div31. (* this is supposed to be the special case of division a/b where a > b *)
 exact div31.
 (* euclidian division remainder *)
 (* again special case for a > b *)
 exact (fun i j => let (_,r) := i/j in r).
 exact (fun i j => let (_,r) := i/j in r).
 (* gcd functions *)
 exact gcd31. (*gcd_gt*)
 exact gcd31. (*gcd*)
 
 (* shift operations *)
 exact addmuldiv31. (*add_mul_div  *)
(*modulo 2^p  *)
 exact (fun p i => 
     match compare31 p 32 with
     | Lt => addmuldiv31 p 0 (addmuldiv31 (31-p) i 0)
     | _ => i
     end).

 (* is i even ? *)
 exact (fun i => let (_,r) := i/2 in 
                          match r ?= 0 with
                          | Eq => true
                          | _ => false
                          end).

 (* square root operations *)
 exact sqrt312. (* sqrt2 *)
 exact sqrt31. (* sqr *)
Defined.

Definition int31_spec : znz_spec int31_op.
Admitted.

 

Module Int31_words <: W0Type.
  Definition w := int31.
  Definition w_op := int31_op.
  Definition w_spec := int31_spec.
End Int31_words.

Module BigN := NMake.Make Int31_words.

Definition bigN := BigN.t.

Delimit Scope bigN_scope with bigN.
Bind Scope bigN_scope with bigN.
Bind Scope bigN_scope with BigN.t.
Bind Scope bigN_scope with BigN.t_.

Notation " i + j " := (BigN.add i j) : bigN_scope.
Notation " i - j " := (BigN.sub i j) : bigN_scope.
Notation " i * j " := (BigN.mul i j) : bigN_scope.
Notation " i / j " := (BigN.div i j) : bigN_scope.
Notation " i ?= j " := (BigN.compare i j) : bigN_scope.

 Theorem succ_pred: forall q,
  (0 < BigN.to_Z q -> 
     BigN.to_Z (BigN.succ (BigN.pred q)) = BigN.to_Z q)%Z.
 intros q Hq.
 rewrite BigN.spec_succ.
 rewrite BigN.spec_pred; auto.
 generalize Hq; set (a := BigN.to_Z q).
 ring_simplify (a - 1 + 1)%Z; auto.
 Qed.
 
