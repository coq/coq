(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

(* Require Import Notations.*)
Require Export ZArith.
Require Export DoubleType.

Unset Boxed Definitions.

Inductive digits : Type := D0 | D1.

Inductive int31 : Type :=
 | I31 : digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> digits ->
         digits -> digits -> digits -> int31.

(* spiwack: Registration of the type of integers, so that the matchs in
   the functions below perform dynamic decompilation (otherwise some segfault
   occur when they are applied to one non-closed term and one closed term *)
Register digits as int31 bits in "coq_int31" by True.
Register int31 as int31 type in "coq_int31" by True.

Delimit Scope int31_scope with int31.
Bind Scope int31_scope with int31.
Open Scope int31_scope.


Definition size := 31%nat.
Definition sizeN := 31%N.

Definition On := I31 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0.
Definition In := I31 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D1.
Definition Tn := I31 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1 D1.
Definition Twon :=  I31 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D1 D0.
Definition T31 :=  I31 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D1 D1 D1 D1 D1.

Definition sneakr b i :=
  match i with
  | I31 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 =>
    I31 b b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30
  end
.

Definition sneakl b i := 
  match i with
    | I31 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 =>
      I31 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b
 end
.

Definition firstl i := 
  match i with
    | I31 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 => b1
  end
.

Definition firstr i := 
  match i with
    | I31 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 => b31
  end
.

Definition iszero i :=
  match i with
  | I31 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 D0 => true
  | _ => false
  end
.


(* abstract definition : smallest b > 0 s.t. phi_inv b = 0  (see below) *)
Definition base := Eval compute in (fix base_aux (counter:nat) :=
                                    match counter with
                                    | 0%nat => 1%Z
                                    | S n => Zdouble (base_aux n)
                                    end) size
.

Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.

Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.



(*recursors*)

Fixpoint recl_aux (iter:nat) (A:Type) (case0:A) (caserec:digits->int31->A->A) 
                           (i:int31)  {struct iter} : A  :=
  match iter with
  | 0%nat => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftl i in
             caserec (firstl i) si (recl_aux next A case0 caserec si)
  end
.
Fixpoint recr_aux (iter:nat) (A:Type) (case0:A) (caserec:digits->int31->A->A) 
                           (i:int31)  {struct iter} : A  :=
  match iter with
  | 0%nat => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftr i in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end
.

Definition recl := recl_aux size.
Definition recr := recr_aux size.


Definition phi :=
  recr Z (0%Z) (fun b _ rec => (match b with | D0 => Zdouble | D1 => Zdouble_plus_one end) rec)
.


(* abstract definition : phi_inv (2n) = 2*phi_inv n /\ 
               phi_inv 2n+1 = 2*(phi_inv n) + 1 *)
Definition phi_inv := 
(* simple incrementation *)
let incr :=
  recr int31 In (fun b si rec => match b with | D0 => sneakl D1 si | D1 => sneakl D0 rec end)
in
fun n =>
 match n with
 | Z0 => On
 | Zpos p =>(fix phi_inv_positive (p:positive) := 
                      match p with
                      | xI q => twice_plus_one (phi_inv_positive q)
                      | xO q => twice (phi_inv_positive q)
                      | xH => In
                      end) p
 | Zneg p =>incr ((fix complement_negative (p:positive) :=
                      match p with
                      | xI q => twice (complement_negative q)
                      | xO q => twice_plus_one (complement_negative q)
                      | xH => twice Tn
                      end) p)
 end
.

(* like phi_inv but returns a double word (zn2z int31) *)
Definition phi_inv2 n :=
  match n with
  | Z0 => W0
  | _ => WW (phi_inv (n/base)%Z) (phi_inv n)
  end
.

(* like phi but takes a double word (two args) *)
Definition phi2 nh nl :=
  ((phi nh)*base+(phi nl))%Z.

(* addition modulo 2^31 *)
Definition add31 (n m : int31) := phi_inv ((phi n)+(phi m)).
Notation "n + m" := (add31 n m) : int31_scope.

(* addition with carry (the result is thus exact) *)
Definition add31c (n m : int31) := 
  let npm := n+m in
  match (phi npm ?= (phi n)+(phi m))%Z with (* spiwack : when executed in non-compiled*)
  | Eq => C0 npm                            (* mode, (phi n)+(phi m) is computed twice*)
  | _ => C1 npm                             (* it may be considered to optimize it *)
  end
.
Notation "n '+c' m" := (add31c n m) (at level 50, no associativity) : int31_scope.

(* addition plus one with carry (the result is thus exact)  *)
Definition add31carryc (n m : int31) :=
  let npmpone_exact := ((phi n)+(phi m)+1)%Z in
  let npmpone := phi_inv npmpone_exact in
  match (phi npmpone ?= npmpone_exact)%Z with
  | Eq => C0 npmpone
  | _ => C1 npmpone
  end
.


(* subtraction modulo 2^31 *)
Definition sub31 (n m : int31) := phi_inv ((phi n)-(phi m)).
Notation "n - m" := (sub31 n m) : int31_scope.

(* subtraction with carry (thus exact) *)
Definition sub31c (n m : int31) := 
  let nmm := n-m in
  match (phi nmm ?= (phi n)-(phi m))%Z with
  | Eq => C0 nmm
  | _ => C1 nmm
  end
.
Notation "n '-c' m" := (sub31c n m) (at level 50, no associativity) : int31_scope.

(* subtraction minus one with carry (thus exact) *)
Definition sub31carryc (n m : int31) :=
  let nmmmone_exact := ((phi n)-(phi m)-1)%Z in
  let nmmmone := phi_inv nmmmone_exact in
  match (phi nmmmone ?= nmmmone_exact)%Z with
  | Eq => C0 nmmmone
  | _ => C1 nmmmone
  end
.


(* multiplication modulo 2^31 *)
Definition mul31 (n m : int31) := phi_inv ((phi n)*(phi m)).
Notation "n * m" := (mul31 n m) : int31_scope.



(* multiplication with double word result (thus exact) *)
Definition mul31c (n m : int31) := phi_inv2 ((phi n)*(phi m)).
Notation "n '*c' m" := (mul31c n m) (at level 40, no associativity) : int31_scope.

(* division of a double size word modulo 2^31 *)
Definition div3121 (nh nl m : int31) := 
  let (q,r) := Zdiv_eucl (phi2 nh nl) (phi m) in
  (phi_inv q, phi_inv r)
.

(* division modulo 2^31 *)
Definition div31 (n m : int31) := 
  let (q,r) := Zdiv_eucl (phi n) (phi m) in
  (phi_inv q, phi_inv r)
.
Notation "n / m" := (div31 n m) : int31_scope.

(* unsigned comparison *)
Definition compare31 (n m : int31) := ((phi n)?=(phi m))%Z.
Notation "n ?= m" := (compare31 n m) (at level 70, no associativity) : int31_scope.

(* [iter_int31 i A f x] = f^i x *)
Definition iter_int31 i A f x :=
  recr (A->A) (fun x => x) (fun b si rec => match b with 
                                            | D0 => fun x => rec (rec x)
                                            | D1 => fun x => f (rec (rec x))
                                            end)
       i x
.

(* [addmuldiv31 p i j] = i*2^p+j/2^(31-p) (modulo 2^31) *)
Definition addmuldiv31 p i j := 
 let (res, _ ) := 
 iter_int31 p (int31*int31) (fun ij => let (i,j) := ij in 
                                    (sneakl (firstl j) i, shiftl j))
          (i,j)
 in
 res
.


Register add31 as int31 plus in "coq_int31" by True.
Register add31c as int31 plusc in "coq_int31" by True.
Register add31carryc as int31 pluscarryc in "coq_int31" by True.
Register sub31 as int31 minus in "coq_int31" by True.
Register sub31c as int31 minusc in "coq_int31" by True.
Register sub31carryc as int31 minuscarryc in "coq_int31" by True.
Register mul31 as int31 times in "coq_int31" by True.
Register mul31c as int31 timesc in "coq_int31" by True.
Register div3121 as int31 div21 in "coq_int31" by True.
Register div31 as int31 div in "coq_int31" by True.
Register compare31 as int31 compare in "coq_int31" by True.
Register addmuldiv31 as int31 addmuldiv in "coq_int31" by True.

Definition gcd31 (i j:int31) :=
  (fix euler (guard:nat) (i j:int31) {struct guard} :=
   match guard with 
   | 0%nat => In
   | S p => match j ?= On with
            | Eq => i
            | _ => euler p j (let (_, r ) := i/j in r)
            end
   end)
  size i j
.

Definition sqrt31 (i:int31) :=
  match i ?= On with
  | Eq =>  On
  | _ =>
   (fix babylon  (guard:nat) (r:int31) {struct guard} :=
     match guard with 
     | 0%nat => r
     | S p =>
       let (quo, _) := i/r in
       match quo ?= r with
       | Eq => r
       | _ => let (avrg, _) := (quo+r)/(Twon) in babylon p avrg
       end
     end)
   size (let (approx, _) := (i/Twon) in approx+In) (* approx + 1 > 0 *) 
  end
.

Definition sqrt312 (ih il:int31) := 
  match (match ih ?= On with | Eq =>  il ?= On | not0 => not0 end) with 
  | Eq => (On, C0 On)
  | _ => let root :=
     (* invariant lower <= r <= upper *)
     let closer_to_upper (r upper lower:int31) :=
	let (quo,_) := (upper-r)/Twon in
	match quo ?= On with
        | Eq => upper
        | _ => r+quo
       end
     in
     let closer_to_lower (r upper lower:int31) :=
        let (quo,_) := (r-lower)/Twon in r-quo 
     in
     (fix dichotomy (guard:nat) (r upper lower:int31) {struct guard} :=
      match guard with
      | 0%nat => r
      | S p => 
         match r*c r with
           | W0 => dichotomy p  
                             (closer_to_upper r upper lower) 
                             upper r             (* because 0 < WW ih il *)
           | WW jh jl => match (match jh ?= ih with 
                                  | Eq => jl ?= il
                                  | noteq => noteq
                                end)
                         with
                           | Eq => r
                           | Lt =>
                             match (r + In)*c (r + In) with
                               | W0 => r (* r = 2^31 - 1 *)
                               | WW jh1 jl1 => 
                                 match (match jh1 ?= ih with 
                                          | Eq => jl1 ?= il 
                                          | noteq => noteq 
                                        end) 
                                 with
                                   | Eq => r + In
                                   | Gt => r
                                   | Lt => dichotomy p
                                        (closer_to_upper r upper lower)
                                        upper r
                                 end
                             end
                           | Gt => dichotomy p 
                                       (closer_to_lower r upper lower) 
                                       r lower
                         end
         end
      end)
     size (let (quo,_) := Tn/Twon in quo) Tn On
     in
     let square := root *c root in
     let rem := match square with
                | W0 => C0 il (* this case should not occure *)
                | WW sh sl => match il -c sl with
                              | C0 reml => match ih - sh ?= On with
                                           | Eq => C0 reml
                                           | _ => C1 reml
                                           end
                              | C1 reml => match ih - sh - In ?= On with
                                           | Eq => C0 reml
                                           | _ => C1 reml
                                           end
                              end
                end
     in
     (root, rem)
  end
.

Definition positive_to_int31 (p:positive) :=
  (fix aux (max_digit:nat) (p:positive) {struct p} : (N*int31)%type := 
   match max_digit with
   | 0%nat => (Npos p, On)
   | S md => match p with
             | xO p' => let (r,i) := aux md p' in (r, Twon*i)
             | xI p' => let (r,i) := aux md p' in (r, Twon*i+In)
             | xH => (N0, In)
             end
   end)
   size p
.

Definition head031 (i:int31) :=
  recl _ (fun _ => T31) (fun b si rec n => match b with 
                                          | D0 => rec (add31 n In)
                                          | D1 => n
                                          end)
       i On
.

Definition tail031 (i:int31) :=
  recr _ (fun _ => T31) (fun b si rec n => match b with 
                                          | D0 => rec (add31 n In)
                                          | D1 => n
                                          end)
       i On
.

Register head031 as int31 head0 in "coq_int31" by True.
Register tail031 as int31 tail0 in "coq_int31" by True. 
