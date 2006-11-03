(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file centralizes the lemmas about [Z], classifying them
    according to the way they can be used in automatic search  *)

(** Lemmas which clearly leads to simplification during proof search are *)
(** declared as Hints. A definite status (Hint or not) for the other lemmas *)
(** remains to be given *)

(** Structure of the file *)
(** - simplification lemmas (only those are declared as Hints) *)
(** - reversible lemmas relating operators *)
(** - useful Bottom-up lemmas              *)
(** - irreversible lemmas with meta-variables *)
(** - unclear or too specific lemmas       *)
(** - lemmas to be used as rewrite rules   *)

(** Lemmas involving positive and compare are not taken into account *)

Require Import BinInt.
Require Import Zorder.
Require Import Zmin.
Require Import Zabs.
Require Import Zcompare.
Require Import Znat.
Require Import auxiliary.
Require Import Zmisc.
Require Import Wf_Z.

(************************************************************************)
(** *                 Simplification lemmas                             *)

(** No subgoal or smaller subgoals                                     *)

Hint Resolve 
  (** ** Reversible simplification lemmas (no loss of information)      *)
  (** Should clearly be declared as hints                               *)
  
  (** Lemmas ending by eq *)
  Zsucc_eq_compat (* :(n,m:Z)`n = m`->`(Zs n) = (Zs m)` *)
  
  (** Lemmas ending by Zgt *)
  Zsucc_gt_compat (* :(n,m:Z)`m > n`->`(Zs m) > (Zs n)` *)
  Zgt_succ (* :(n:Z)`(Zs n) > n` *)
  Zorder.Zgt_pos_0 (* :(p:positive)`(POS p) > 0` *)
  Zplus_gt_compat_l (* :(n,m,p:Z)`n > m`->`p+n > p+m` *)
  Zplus_gt_compat_r (* :(n,m,p:Z)`n > m`->`n+p > m+p` *)
  
  (** Lemmas ending by Zlt *)
  Zlt_succ (* :(n:Z)`n < (Zs n)` *)
  Zsucc_lt_compat (* :(n,m:Z)`n < m`->`(Zs n) < (Zs m)` *)
  Zlt_pred (* :(n:Z)`(Zpred n) < n` *)
  Zplus_lt_compat_l (* :(n,m,p:Z)`n < m`->`p+n < p+m` *)
  Zplus_lt_compat_r (* :(n,m,p:Z)`n < m`->`n+p < m+p` *)
  
  (** Lemmas ending by Zle *)
  Zle_0_nat (* :(n:nat)`0 <= (inject_nat n)` *)
  Zorder.Zle_0_pos (* :(p:positive)`0 <= (POS p)` *)
  Zle_refl (* :(n:Z)`n <= n` *)
  Zle_succ (* :(n:Z)`n <= (Zs n)` *)
  Zsucc_le_compat (* :(n,m:Z)`m <= n`->`(Zs m) <= (Zs n)` *)
  Zle_pred (* :(n:Z)`(Zpred n) <= n` *)
  Zle_min_l (* :(n,m:Z)`(Zmin n m) <= n` *)
  Zle_min_r (* :(n,m:Z)`(Zmin n m) <= m` *)
  Zplus_le_compat_l (* :(n,m,p:Z)`n <= m`->`p+n <= p+m` *)
  Zplus_le_compat_r (* :(a,b,c:Z)`a <= b`->`a+c <= b+c` *)
  Zabs_pos (* :(x:Z)`0 <= |x|` *)
  
  (** ** Irreversible simplification lemmas *)
  (** Probably to be declared as hints, when no other simplification is possible *)
  
  (** Lemmas ending by eq *)
  BinInt.Z_eq_mult (* :(x,y:Z)`y = 0`->`y*x = 0` *)
  Zplus_eq_compat (* :(n,m,p,q:Z)`n = m`->`p = q`->`n+p = m+q` *)
  
  (** Lemmas ending by Zge *)
  Zorder.Zmult_ge_compat_r (* :(a,b,c:Z)`a >= b`->`c >= 0`->`a*c >= b*c` *)
  Zorder.Zmult_ge_compat_l (* :(a,b,c:Z)`a >= b`->`c >= 0`->`c*a >= c*b` *)
  Zorder.Zmult_ge_compat (* :
      (a,b,c,d:Z)`a >= c`->`b >= d`->`c >= 0`->`d >= 0`->`a*b >= c*d` *)
  
  (** Lemmas ending by Zlt *)
  Zorder.Zmult_gt_0_compat (* :(a,b:Z)`a > 0`->`b > 0`->`a*b > 0` *)
  Zlt_lt_succ (* :(n,m:Z)`n < m`->`n < (Zs m)` *)
  
  (** Lemmas ending by Zle *)
  Zorder.Zmult_le_0_compat (* :(x,y:Z)`0 <= x`->`0 <= y`->`0 <= x*y` *)
  Zorder.Zmult_le_compat_r (* :(a,b,c:Z)`a <= b`->`0 <= c`->`a*c <= b*c` *)
  Zorder.Zmult_le_compat_l (* :(a,b,c:Z)`a <= b`->`0 <= c`->`c*a <= c*b` *)
  Zplus_le_0_compat (* :(x,y:Z)`0 <= x`->`0 <= y`->`0 <= x+y` *)
  Zle_le_succ (* :(x,y:Z)`x <= y`->`x <= (Zs y)` *)
  Zplus_le_compat (* :(n,m,p,q:Z)`n <= m`->`p <= q`->`n+p <= m+q` *)
  
  : zarith.
  
(**********************************************************************)
(** *        Reversible lemmas relating operators                     *)
(** Probably to be declared as hints but need to define precedences   *)

(** ** Conversion between comparisons/predicates and arithmetic operators *)

(** Lemmas ending by eq *)
(** 
<<
Zegal_left: (x,y:Z)`x = y`->`x+(-y) = 0`
Zabs_eq: (x:Z)`0 <= x`->`|x| = x`
Zeven_div2: (x:Z)(Zeven x)->`x = 2*(Zdiv2 x)`
Zodd_div2: (x:Z)`x >= 0`->(Zodd x)->`x = 2*(Zdiv2 x)+1`
>>
*)

(** Lemmas ending by Zgt *)
(** 
<<
Zgt_left_rev: (x,y:Z)`x+(-y) > 0`->`x > y`
Zgt_left_gt: (x,y:Z)`x > y`->`x+(-y) > 0`
>>
*)

(** Lemmas ending by Zlt *)
(** 
<<
Zlt_left_rev: (x,y:Z)`0 < y+(-x)`->`x < y`
Zlt_left_lt: (x,y:Z)`x < y`->`0 < y+(-x)`
Zlt_O_minus_lt: (n,m:Z)`0 < n-m`->`m < n`
>>
*)

(** Lemmas ending by Zle *)
(** 
<<
Zle_left: (x,y:Z)`x <= y`->`0 <= y+(-x)`
Zle_left_rev: (x,y:Z)`0 <= y+(-x)`->`x <= y`
Zlt_left: (x,y:Z)`x < y`->`0 <= y+(-1)+(-x)`
Zge_left: (x,y:Z)`x >= y`->`0 <= x+(-y)`
Zgt_left: (x,y:Z)`x > y`->`0 <= x+(-1)+(-y)`
>>
*)

(** ** Conversion between nat comparisons and Z comparisons *)

(** Lemmas ending by eq *)
(** 
<<
inj_eq: (x,y:nat)x=y->`(inject_nat x) = (inject_nat y)`
>>
*)

(** Lemmas ending by Zge *)
(** 
<<
inj_ge: (x,y:nat)(ge x y)->`(inject_nat x) >= (inject_nat y)`
>>
*)

(** Lemmas ending by Zgt *)
(** 
<<
inj_gt: (x,y:nat)(gt x y)->`(inject_nat x) > (inject_nat y)`
>>
*)

(** Lemmas ending by Zlt *)
(** 
<<
inj_lt: (x,y:nat)(lt x y)->`(inject_nat x) < (inject_nat y)`
>>
*)

(** Lemmas ending by Zle *)
(** 
<<
inj_le: (x,y:nat)(le x y)->`(inject_nat x) <= (inject_nat y)`
>>
*)

(** ** Conversion between comparisons *)

(** Lemmas ending by Zge *)
(** 
<<
not_Zlt: (x,y:Z)~`x < y`->`x >= y`
Zle_ge: (m,n:Z)`m <= n`->`n >= m`
>>
*)

(** Lemmas ending by Zgt *)
(** 
<<
Zle_gt_S: (n,p:Z)`n <= p`->`(Zs p) > n`
not_Zle: (x,y:Z)~`x <= y`->`x > y`
Zlt_gt: (m,n:Z)`m < n`->`n > m`
Zle_S_gt: (n,m:Z)`(Zs n) <= m`->`m > n`
>>
*)

(** Lemmas ending by Zlt *)
(** 
<<
not_Zge: (x,y:Z)~`x >= y`->`x < y`
Zgt_lt: (m,n:Z)`m > n`->`n < m`
Zle_lt_n_Sm: (n,m:Z)`n <= m`->`n < (Zs m)`
>>
*)

(** Lemmas ending by Zle *)
(** 
<<
Zlt_ZERO_pred_le_ZERO: (x:Z)`0 < x`->`0 <= (Zpred x)`
not_Zgt: (x,y:Z)~`x > y`->`x <= y`
Zgt_le_S: (n,p:Z)`p > n`->`(Zs n) <= p`
Zgt_S_le: (n,p:Z)`(Zs p) > n`->`n <= p`
Zge_le: (m,n:Z)`m >= n`->`n <= m`
Zlt_le_S: (n,p:Z)`n < p`->`(Zs n) <= p`
Zlt_n_Sm_le: (n,m:Z)`n < (Zs m)`->`n <= m`
Zlt_le_weak: (n,m:Z)`n < m`->`n <= m`
Zle_refl: (n,m:Z)`n = m`->`n <= m`
>>
*)

(** ** Irreversible simplification involving several comparaisons *)
(**    useful with clear precedences *)

(** Lemmas ending by Zlt *)
(** 
<<
Zlt_le_reg :(a,b,c,d:Z)`a < b`->`c <= d`->`a+c < b+d`
Zle_lt_reg : (a,b,c,d:Z)`a <= b`->`c < d`->`a+c < b+d`
>>
*)

(** ** What is decreasing here ? *)

(** Lemmas ending by eq *)
(** 
<<
Zplus_minus: (n,m,p:Z)`n = m+p`->`p = n-m`
>>
*)

(** Lemmas ending by Zgt *)
(** 
<<
Zgt_pred: (n,p:Z)`p > (Zs n)`->`(Zpred p) > n`
>>
*)

(** Lemmas ending by Zlt *)
(** 
<<
Zlt_pred: (n,p:Z)`(Zs n) < p`->`n < (Zpred p)`
>>
*)

(**********************************************************************)
(** *                Useful Bottom-up lemmas                          *)

(** ** Bottom-up simplification: should be used *)

(** Lemmas ending by eq *)
(** 
<< 
Zeq_add_S: (n,m:Z)`(Zs n) = (Zs m)`->`n = m`
Zsimpl_plus_l: (n,m,p:Z)`n+m = n+p`->`m = p`
Zplus_unit_left: (n,m:Z)`n+0 = m`->`n = m`
Zplus_unit_right: (n,m:Z)`n = m+0`->`n = m`
>>
*)

(** Lemmas ending by Zgt *)
(** 
<< 
Zsimpl_gt_plus_l: (n,m,p:Z)`p+n > p+m`->`n > m`
Zsimpl_gt_plus_r: (n,m,p:Z)`n+p > m+p`->`n > m`
Zgt_S_n: (n,p:Z)`(Zs p) > (Zs n)`->`p > n` 
>> 
*)

(** Lemmas ending by Zlt *)
(** 
<< 
Zsimpl_lt_plus_l: (n,m,p:Z)`p+n < p+m`->`n < m`
Zsimpl_lt_plus_r: (n,m,p:Z)`n+p < m+p`->`n < m`
Zlt_S_n: (n,m:Z)`(Zs n) < (Zs m)`->`n < m` 
>> 
*)

(** Lemmas ending by Zle *)
(** << Zsimpl_le_plus_l: (p,n,m:Z)`p+n <= p+m`->`n <= m`
Zsimpl_le_plus_r: (p,n,m:Z)`n+p <= m+p`->`n <= m`
Zle_S_n: (n,m:Z)`(Zs m) <= (Zs n)`->`m <= n` >> *)

(** ** Bottom-up irreversible (syntactic) simplification *)

(** Lemmas ending by Zle *)
(** 
<<
Zle_trans_S: (n,m:Z)`(Zs n) <= m`->`n <= m`
>>
*)

(** ** Other unclearly simplifying lemmas *)

(** Lemmas ending by Zeq *)
(** 
<< 
Zmult_eq: (x,y:Z)`x <> 0`->`y*x = 0`->`y = 0` 
>> 
*)

(* Lemmas ending by Zgt *)
(** 
<< 
Zmult_gt: (x,y:Z)`x > 0`->`x*y > 0`->`y > 0`
>>
*)

(* Lemmas ending by Zlt *)
(** 
<< 
pZmult_lt: (x,y:Z)`x > 0`->`0 < y*x`->`0 < y`
>> 
*)

(* Lemmas ending by Zle *)
(** 
<< 
Zmult_le: (x,y:Z)`x > 0`->`0 <= y*x`->`0 <= y`
OMEGA1: (x,y:Z)`x = y`->`0 <= x`->`0 <= y`
>> 
*)


(**********************************************************************)
(** *        Irreversible lemmas with meta-variables                  *)
(** To be used by EAuto                                               *) 

(* Hints Immediate *)
(** Lemmas ending by eq *)
(** 
<< 
Zle_antisym: (n,m:Z)`n <= m`->`m <= n`->`n = m`
>>
*)

(** Lemmas ending by Zge *)
(** 
<< 
Zge_trans: (n,m,p:Z)`n >= m`->`m >= p`->`n >= p`
>> 
*)

(** Lemmas ending by Zgt *)
(** 
<< 
Zgt_trans: (n,m,p:Z)`n > m`->`m > p`->`n > p`
Zgt_trans_S: (n,m,p:Z)`(Zs n) > m`->`m > p`->`n > p`
Zle_gt_trans: (n,m,p:Z)`m <= n`->`m > p`->`n > p`
Zgt_le_trans: (n,m,p:Z)`n > m`->`p <= m`->`n > p`
>> 
*)

(** Lemmas ending by Zlt *)
(** 
<< 
Zlt_trans: (n,m,p:Z)`n < m`->`m < p`->`n < p`
Zlt_le_trans: (n,m,p:Z)`n < m`->`m <= p`->`n < p`
Zle_lt_trans: (n,m,p:Z)`n <= m`->`m < p`->`n < p`
>> 
*)

(** Lemmas ending by Zle *)
(** 
<< 
Zle_trans: (n,m,p:Z)`n <= m`->`m <= p`->`n <= p`
>> 
*)


(**********************************************************************)
(** *               Unclear or too specific lemmas                    *)
(** Not to be used ?                                                  *)

(** ** Irreversible and too specific (not enough regular) *)

(** Lemmas ending by Zle *)
(**
<<
Zle_mult: (x,y:Z)`x > 0`->`0 <= y`->`0 <= y*x`
Zle_mult_approx: (x,y,z:Z)`x > 0`->`z > 0`->`0 <= y`->`0 <= y*x+z`
OMEGA6: (x,y,z:Z)`0 <= x`->`y = 0`->`0 <= x+y*z`
OMEGA7: (x,y,z,t:Z)`z > 0`->`t > 0`->`0 <= x`->`0 <= y`->`0 <= x*z+y*t`
>>
*)

(** ** Expansion and too specific ? *)

(** Lemmas ending by Zge *)
(**
<<
Zge_mult_simpl: (a,b,c:Z)`c > 0`->`a*c >= b*c`->`a >= b`
>>
*)

(** Lemmas ending by Zgt *)
(**
<<
Zgt_mult_simpl: (a,b,c:Z)`c > 0`->`a*c > b*c`->`a > b`
Zgt_square_simpl: (x,y:Z)`x >= 0`->`y >= 0`->`x*x > y*y`->`x > y`
>>
*)

(** Lemmas ending by Zle *)
(**
<<
Zle_mult_simpl: (a,b,c:Z)`c > 0`->`a*c <= b*c`->`a <= b`
Zmult_le_approx: (x,y,z:Z)`x > 0`->`x > z`->`0 <= y*x+z`->`0 <= y`
>>
*)

(** ** Reversible but too specific ? *)

(** Lemmas ending by Zlt *)
(**
<<
Zlt_minus: (n,m:Z)`0 < m`->`n-m < n`
>>
*)

(**********************************************************************)
(** *               Lemmas to be used as rewrite rules                *)
(** but can also be used as hints                                     *)

(** Left-to-right simplification lemmas (a symbol disappears) *)

(**
<<
Zcompare_n_S: (n,m:Z)(Zcompare (Zs n) (Zs m))=(Zcompare n m)
Zmin_n_n: (n:Z)`(Zmin n n) = n`
Zmult_1_n: (n:Z)`1*n = n`
Zmult_n_1: (n:Z)`n*1 = n`
Zminus_plus: (n,m:Z)`n+m-n = m`
Zle_plus_minus: (n,m:Z)`n+(m-n) = m`
Zopp_Zopp: (x:Z)`(-(-x)) = x`
Zero_left: (x:Z)`0+x = x`
Zero_right: (x:Z)`x+0 = x`
Zplus_inverse_r: (x:Z)`x+(-x) = 0`
Zplus_inverse_l: (x:Z)`(-x)+x = 0`
Zopp_intro: (x,y:Z)`(-x) = (-y)`->`x = y`
Zmult_one: (x:Z)`1*x = x`
Zero_mult_left: (x:Z)`0*x = 0`
Zero_mult_right: (x:Z)`x*0 = 0`
Zmult_Zopp_Zopp: (x,y:Z)`(-x)*(-y) = x*y`
>>
*)

(** Right-to-left simplification lemmas (a symbol disappears) *)

(**
<<
Zpred_Sn: (m:Z)`m = (Zpred (Zs m))`
Zs_pred: (n:Z)`n = (Zs (Zpred n))`
Zplus_n_O: (n:Z)`n = n+0`
Zmult_n_O: (n:Z)`0 = n*0`
Zminus_n_O: (n:Z)`n = n-0`
Zminus_n_n: (n:Z)`0 = n-n`
Zred_factor6: (x:Z)`x = x+0`
Zred_factor0: (x:Z)`x = x*1`
>>
*)

(** Unclear orientation (no symbol disappears) *)

(**
<<
Zplus_n_Sm: (n,m:Z)`(Zs (n+m)) = n+(Zs m)`
Zmult_n_Sm: (n,m:Z)`n*m+n = n*(Zs m)`
Zmin_SS: (n,m:Z)`(Zs (Zmin n m)) = (Zmin (Zs n) (Zs m))`
Zplus_assoc_l: (n,m,p:Z)`n+(m+p) = n+m+p`
Zplus_assoc_r: (n,m,p:Z)`n+m+p = n+(m+p)`
Zplus_permute: (n,m,p:Z)`n+(m+p) = m+(n+p)`
Zplus_Snm_nSm: (n,m:Z)`(Zs n)+m = n+(Zs m)`
Zminus_plus_simpl: (n,m,p:Z)`n-m = p+n-(p+m)`
Zminus_Sn_m: (n,m:Z)`(Zs (n-m)) = (Zs n)-m`
Zmult_plus_distr_l: (n,m,p:Z)`(n+m)*p = n*p+m*p`
Zmult_minus_distr: (n,m,p:Z)`(n-m)*p = n*p-m*p`
Zmult_assoc_r: (n,m,p:Z)`n*m*p = n*(m*p)`
Zmult_assoc_l: (n,m,p:Z)`n*(m*p) = n*m*p`
Zmult_permute: (n,m,p:Z)`n*(m*p) = m*(n*p)`
Zmult_Sm_n: (n,m:Z)`n*m+m = (Zs n)*m`
Zmult_Zplus_distr: (x,y,z:Z)`x*(y+z) = x*y+x*z`
Zmult_plus_distr: (n,m,p:Z)`(n+m)*p = n*p+m*p`
Zopp_Zplus: (x,y:Z)`(-(x+y)) = (-x)+(-y)`
Zplus_sym: (x,y:Z)`x+y = y+x`
Zplus_assoc: (x,y,z:Z)`x+(y+z) = x+y+z`
Zmult_sym: (x,y:Z)`x*y = y*x`
Zmult_assoc: (x,y,z:Z)`x*(y*z) = x*y*z`
Zopp_Zmult: (x,y:Z)`(-x)*y = (-(x*y))`
Zplus_S_n: (x,y:Z)`(Zs x)+y = (Zs (x+y))`
Zopp_one: (x:Z)`(-x) = x*(-1)`
Zopp_Zmult_r: (x,y:Z)`(-(x*y)) = x*(-y)`
Zmult_Zopp_left: (x,y:Z)`(-x)*y = x*(-y)`
Zopp_Zmult_l: (x,y:Z)`(-(x*y)) = (-x)*y`
Zred_factor1: (x:Z)`x+x = x*2`
Zred_factor2: (x,y:Z)`x+x*y = x*(1+y)`
Zred_factor3: (x,y:Z)`x*y+x = x*(1+y)`
Zred_factor4: (x,y,z:Z)`x*y+x*z = x*(y+z)`
Zminus_Zplus_compatible: (x,y,n:Z)`x+n-(y+n) = x-y`
Zmin_plus: (x,y,n:Z)`(Zmin (x+n) (y+n)) = (Zmin x y)+n`
>>
*)

(** nat <-> Z *)
(**
<<
inj_S: (y:nat)`(inject_nat (S y)) = (Zs (inject_nat y))`
inj_plus: (x,y:nat)`(inject_nat (plus x y)) = (inject_nat x)+(inject_nat y)`
inj_mult: (x,y:nat)`(inject_nat (mult x y)) = (inject_nat x)*(inject_nat y)`
inj_minus1:
 (x,y:nat)(le y x)->`(inject_nat (minus x y)) = (inject_nat x)-(inject_nat y)`
inj_minus2: (x,y:nat)(gt y x)->`(inject_nat (minus x y)) = 0`
>>
*)

(** Too specific ? *)
(**
<<
Zred_factor5: (x,y:Z)`x*0+y = y`
>>
*)

