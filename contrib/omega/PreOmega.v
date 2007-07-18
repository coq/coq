Require Import Arith Max Min ZArith_base NArith Nnat.

Open Local Scope Z_scope.


(** * zify: the Z-ification tactic *)

(* This tactic searches for nat and N and positive elements in the goal and 
   translates everything into Z. It is meant as a pre-processor for 
   (r)omega; for instance a positivity hypothesis is added whenever
     - a multiplication is encountered
     - an atom is encountered (that is a variable or an unknown construct)

   Recognized relations (can be handled as deeply as allowed by setoid rewrite):
     - { eq, le, lt, ge, gt } on { Z, positive, N, nat }
   
   Recognized operations: 
     - on Z: Zmin, Zmax, Zabs, Zsgn are translated in term of <= < =
     - on nat: + * - S O pred min max nat_of_P nat_of_N Zabs_nat
     - on positive: Zneg Zpos xI xO xH + * - Psucc Ppred Pmin Pmax P_of_succ_nat
     - on N: N0 Npos + * - Nsucc Nmin Nmax N_of_nat Zabs_N
*)




(** I) translation of Zmax, Zmin, Zabs, Zsgn into recognized equations *)

Ltac zify_unop_core t thm a := 
 (* Let's introduce the specification theorem for t *)
 let H:= fresh "H" in assert (H:=thm a); 
 (* Then we replace (t a) everywhere with a fresh variable *)
 let z := fresh "z" in set (z:=t a) in *; clearbody z.

Ltac zify_unop_var_or_term t thm a := 
 (* If a is a variable, no need for aliasing *)
 let za := fresh "z" in 
 (rename a into za; rename za into a; zify_unop_core t thm a) ||
 (* Otherwise, a is a complex term: we alias it. *)
 (remember a as za; zify_unop_core t thm za).

Ltac zify_unop t thm a := 
 (* if a is a scalar, we can simply reduce the unop *)
 let isz := isZcst a in 
 match isz with 
  | true => simpl (t a) in *
  | _ => zify_unop_var_or_term t thm a
 end.

Ltac zify_unop_nored t thm a := 
 (* in this version, we don't try to reduce the unop (that can be (Zplus x)) *)
 let isz := isZcst a in 
 match isz with 
  | true => zify_unop_core t thm a
  | _ => zify_unop_var_or_term t thm a
 end.

Ltac zify_binop t thm a b:=
 (* works as zify_unop, except that we should be careful when
    dealing with b, since it can be equal to a *)
 let isza := isZcst a in 
 match isza with 
   | true => zify_unop (t a) (thm a) b
   | _ => 
       let za := fresh "z" in 
       (rename a into za; rename za into a; zify_unop_nored (t a) (thm a) b) ||
       (remember a as za; match goal with 
         | H : za = b |- _ => zify_unop_nored (t za) (thm za) za
         | _ => zify_unop_nored (t za) (thm za) b
        end)
 end.

Ltac zify_op_1 := 
  match goal with 
   | |- context [ Zmax ?a ?b ] => zify_binop Zmax Zmax_spec a b
   | H : context [ Zmax ?a ?b ] |- _ => zify_binop Zmax Zmax_spec a b
   | |- context [ Zmin ?a ?b ] => zify_binop Zmin Zmin_spec a b
   | H : context [ Zmin ?a ?b ] |- _ => zify_binop Zmin Zmin_spec a b
   | |- context [ Zsgn ?a ] => zify_unop Zsgn Zsgn_spec a
   | H : context [ Zsgn ?a ] |- _ => zify_unop Zsgn Zsgn_spec a
   | |- context [ Zabs ?a ] => zify_unop Zabs Zabs_spec a
   | H : context [ Zabs ?a ] |- _ => zify_unop Zabs Zabs_spec a
  end.

Ltac zify_op := repeat zify_op_1.





(** II) Conversion from nat to Z *)


Definition Z_of_nat' := Z_of_nat.

Ltac hide_Z_of_nat t := 
  let z := fresh "z" in set (z:=Z_of_nat t) in *; 
  change Z_of_nat with Z_of_nat' in z; 
  unfold z in *; clear z.

Ltac zify_nat_rel := 
 match goal with 
  (* I: equalities *)
  | H : (@eq nat ?a ?b) |- _ => generalize (inj_eq _ _ H); clear H; intro H
  | |- (@eq nat ?a ?b) => apply (inj_eq_rev a b)
  | H : context [ @eq nat ?a ?b ] |- _ => rewrite (inj_eq_iff a b) in H
  | |- context [ @eq nat ?a ?b ] =>       rewrite (inj_eq_iff a b)
  (* II: less than *)
  | H : (lt ?a ?b) |- _ => generalize (inj_lt _ _ H); clear H; intro H
  | |- (lt ?a ?b) => apply (inj_lt_rev a b)
  | H : context [ lt ?a ?b ] |- _ => rewrite (inj_lt_iff a b) in H
  | |- context [ lt ?a ?b ] =>       rewrite (inj_lt_iff a b)
  (* III: less or equal *)
  | H : (le ?a ?b) |- _ => generalize (inj_le _ _ H); clear H; intro H
  | |- (le ?a ?b) => apply (inj_le_rev a b)
  | H : context [ le ?a ?b ] |- _ => rewrite (inj_le_iff a b) in H
  | |- context [ le ?a ?b ] =>       rewrite (inj_le_iff a b)
  (* IV: greater than *)
  | H : (gt ?a ?b) |- _ => generalize (inj_gt _ _ H); clear H; intro H
  | |- (gt ?a ?b) => apply (inj_gt_rev a b)
  | H : context [ gt ?a ?b ] |- _ => rewrite (inj_gt_iff a b) in H
  | |- context [ gt ?a ?b ] =>       rewrite (inj_gt_iff a b)
  (* V: greater or equal *)
  | H : (ge ?a ?b) |- _ => generalize (inj_ge _ _ H); clear H; intro H
  | |- (ge ?a ?b) => apply (inj_ge_rev a b)
  | H : context [ ge ?a ?b ] |- _ => rewrite (inj_ge_iff a b) in H
  | |- context [ ge ?a ?b ] =>       rewrite (inj_ge_iff a b)
 end.

Ltac zify_nat_op := 
 match goal with 
  (* misc type conversions: positive/N/Z to nat *)
  | H : context [ Z_of_nat (nat_of_P ?a) ] |- _ => rewrite <- (Zpos_eq_Z_of_nat_o_nat_of_P a) in H
  | |- context [ Z_of_nat (nat_of_P ?a) ] => rewrite <- (Zpos_eq_Z_of_nat_o_nat_of_P a)
  | H : context [ Z_of_nat (nat_of_N ?a) ] |- _ => rewrite (Z_of_nat_of_N a) in H
  | |- context [ Z_of_nat (nat_of_N ?a) ] => rewrite (Z_of_nat_of_N a)
  | H : context [ Z_of_nat (Zabs_nat ?a) ] |- _ => rewrite (inj_Zabs_nat a) in H
  | |- context [ Z_of_nat (Zabs_nat ?a) ] => rewrite (inj_Zabs_nat a)

  (* plus -> Zplus *)
  | H : context [ Z_of_nat (plus ?a ?b) ] |- _ => rewrite (inj_plus a b) in H
  | |- context [ Z_of_nat (plus ?a ?b) ] => rewrite (inj_plus a b)

  (* min -> Zmin *)
  | H : context [ Z_of_nat (min ?a ?b) ] |- _ => rewrite (inj_min a b) in H
  | |- context [ Z_of_nat (min ?a ?b) ] => rewrite (inj_min a b)

  (* max -> Zmax *)
  | H : context [ Z_of_nat (max ?a ?b) ] |- _ => rewrite (inj_max a b) in H
  | |- context [ Z_of_nat (max ?a ?b) ] => rewrite (inj_max a b)

  (* minus -> Zmax (Zminus ... ...) 0 *)
  | H : context [ Z_of_nat (minus ?a ?b) ] |- _ => rewrite (inj_minus a b) in H
  | |- context [ Z_of_nat (minus ?a ?b) ] => rewrite (inj_minus a b)

  (* pred -> minus ... -1 -> Zmax (Zminus ... -1) 0 *)
  | H : context [ Z_of_nat (pred ?a) ] |- _ => rewrite (pred_of_minus a) in H
  | |- context [ Z_of_nat (pred ?a) ] => rewrite (pred_of_minus a)

  (* mult -> Zmult and a positivity hypothesis *)
  | H : context [ Z_of_nat (mult ?a ?b) ] |- _ => 
        let H:= fresh "H" in 
        assert (H:=Zle_0_nat (mult a b)); rewrite (inj_mult a b) in *
  | |- context [ Z_of_nat (mult ?a ?b) ] => 
        let H:= fresh "H" in 
        assert (H:=Zle_0_nat (mult a b)); rewrite (inj_mult a b) in *

  (* O -> Z0 *)
  | H : context [ Z_of_nat O ] |- _ => simpl (Z_of_nat O) in H
  | |- context [ Z_of_nat O ] => simpl (Z_of_nat O)

  (* S -> number or Zsucc *)
  | H : context [ Z_of_nat (S ?a) ] |- _ => 
     let isnat := isnatcst a in 
     match isnat with 
      | true => simpl (Z_of_nat (S a)) in H
      | _ => rewrite (inj_S a) in H
     end
  | |- context [ Z_of_nat (S ?a) ] => 
     let isnat := isnatcst a in 
     match isnat with 
      | true => simpl (Z_of_nat (S a))
      | _ => rewrite (inj_S a)
     end

  (* atoms of type nat : we add a positivity condition (if not already there) *) 
  | H : context [ Z_of_nat ?a ] |- _ => 
        match goal with 
          | H' : 0 <= Z_of_nat a |- _ => hide_Z_of_nat a
          | H' : 0 <= Z_of_nat' a |- _ => fail
          | _ => let H:= fresh "H" in
                 assert (H:=Zle_0_nat a); hide_Z_of_nat a
        end
  | |- context [ Z_of_nat ?a ] => 
        match goal with 
          | H' : 0 <= Z_of_nat a |- _ => hide_Z_of_nat a
          | H' : 0 <= Z_of_nat' a |- _ => fail
          | _ => let H:= fresh "H" in
                 assert (H:=Zle_0_nat a); hide_Z_of_nat a
        end
 end.

Ltac zify_nat := repeat zify_nat_rel; repeat zify_nat_op; unfold Z_of_nat' in *.




(* III) conversion from positive to Z *) 

Definition Zpos' := Zpos.
Definition Zneg' := Zneg.

Ltac hide_Zpos t := 
  let z := fresh "z" in set (z:=Zpos t) in *; 
  change Zpos with Zpos' in z; 
  unfold z in *; clear z.

Ltac zify_positive_rel := 
 match goal with 
  (* I: equalities *)
  | H : (@eq positive ?a ?b) |- _ => generalize (Zpos_eq _ _ H); clear H; intro H
  | |- (@eq positive ?a ?b) => apply (Zpos_eq_rev a b)
  | H : context [ @eq positive ?a ?b ] |- _ => rewrite (Zpos_eq_iff a b) in H
  | |- context [ @eq positive ?a ?b ] =>       rewrite (Zpos_eq_iff a b)
  (* II: less than *)
  | H : context [ (?a<?b)%positive ] |- _ => change (a<b)%positive with (Zpos a<Zpos b) in H
  | |- context [ (?a<?b)%positive ] => change (a<b)%positive with (Zpos a<Zpos b)
  (* III: less or equal *)
  | H : context [ (?a<=?b)%positive ] |- _ => change (a<=b)%positive with (Zpos a<=Zpos b) in H
  | |- context [ (?a<=?b)%positive ] => change (a<=b)%positive with (Zpos a<=Zpos b)
  (* IV: greater than *)
  | H : context [ (?a>?b)%positive ] |- _ => change (a>b)%positive with (Zpos a>Zpos b) in H
  | |- context [ (?a>?b)%positive ] => change (a>b)%positive with (Zpos a>Zpos b)
  (* V: greater or equal *)
  | H : context [ (?a>=?b)%positive ] |- _ => change (a>=b)%positive with (Zpos a>=Zpos b) in H
  | |- context [ (?a>=?b)%positive ] => change (a>=b)%positive with (Zpos a>=Zpos b)
 end.

Ltac zify_positive_op := 
 match goal with 
  (* Zneg -> -Zpos (except for numbers) *)
  | H : context [ Zneg ?a ] |- _ => 
     let isp := isPcst a in 
     match isp with 
      | true => change (Zneg a) with (Zneg' a) in H
      | _ => change (Zneg a) with (- Zpos a) in H
     end
  | |- context [ Zneg ?a ] => 
     let isp := isPcst a in 
     match isp with 
      | true => change (Zneg a) with (Zneg' a)
      | _ => change (Zneg a) with (- Zpos a)
     end

  (* misc type conversions: nat to positive *)
  | H : context [ Zpos (P_of_succ_nat ?a) ] |- _ => rewrite (Zpos_P_of_succ_nat a) in H
  | |- context [ Zpos (P_of_succ_nat ?a) ] => rewrite (Zpos_P_of_succ_nat a)

  (* Pplus -> Zplus *)
  | H : context [ Zpos (Pplus ?a ?b) ] |- _ => change (Zpos (Pplus a b)) with (Zplus (Zpos a) (Zpos b)) in H
  | |- context [ Zpos (Pplus ?a ?b) ] => change (Zpos (Pplus a b)) with (Zplus (Zpos a) (Zpos b))

  (* Pmin -> Zmin *)
  | H : context [ Zpos (Pmin ?a ?b) ] |- _ => rewrite (Zpos_min a b) in H
  | |- context [ Zpos (Pmin ?a ?b) ] => rewrite (Zpos_min a b)

  (* Pmax -> Zmax *)
  | H : context [ Zpos (Pmax ?a ?b) ] |- _ => rewrite (Zpos_max a b) in H
  | |- context [ Zpos (Pmax ?a ?b) ] => rewrite (Zpos_max a b)

  (* Pminus -> Zmax 1 (Zminus ... ...) *)
  | H : context [ Zpos (Pminus ?a ?b) ] |- _ => rewrite (Zpos_minus a b) in H
  | |- context [ Zpos (Pminus ?a ?b) ] => rewrite (Zpos_minus a b)

  (* Psucc -> Zsucc *) 
  | H : context [ Zpos (Psucc ?a) ] |- _ => rewrite (Zpos_succ_morphism a) in H
  | |- context [ Zpos (Psucc ?a) ] => rewrite (Zpos_succ_morphism a)

  (* Ppred -> Pminus ... -1 -> Zmax 1 (Zminus ... - 1) *)
  | H : context [ Zpos (Ppred ?a) ] |- _ => rewrite (Ppred_minus a) in H
  | |- context [ Zpos (Ppred ?a) ] => rewrite (Ppred_minus a)
 
  (* Pmult -> Zmult and a positivity hypothesis *)
  | H : context [ Zpos (Pmult ?a ?b) ] |- _ => 
        let H:= fresh "H" in 
        assert (H:=Zgt_pos_0 (Pmult a b)); rewrite (Zpos_mult_morphism a b) in *
  | |- context [ Zpos (Pmult ?a ?b) ] => 
        let H:= fresh "H" in 
        assert (H:=Zgt_pos_0 (Pmult a b)); rewrite (Zpos_mult_morphism a b) in *

  (* xO *)
  | H : context [ Zpos (xO ?a) ] |- _ => 
     let isp := isPcst a in 
     match isp with 
      | true => change (Zpos (xO a)) with (Zpos' (xO a)) in H
      | _ => rewrite (Zpos_xO a) in H
     end
  | |- context [ Zpos (xO ?a) ] => 
     let isp := isPcst a in 
     match isp with 
      | true => change (Zpos (xO a)) with (Zpos' (xO a))
      | _ => rewrite (Zpos_xO a)
     end
  (* xI *) 
  | H : context [ Zpos (xI ?a) ] |- _ => 
     let isp := isPcst a in 
     match isp with 
      | true => change (Zpos (xI a)) with (Zpos' (xI a)) in H
      | _ => rewrite (Zpos_xI a) in H
     end
  | |- context [ Zpos (xI ?a) ] => 
     let isp := isPcst a in 
     match isp with 
      | true => change (Zpos (xI a)) with (Zpos' (xI a))
      | _ => rewrite (Zpos_xI a)
     end

  (* xI : nothing to do, just prevent adding a useless positivity condition *)
  | H : context [ Zpos xH ] |- _ => hide_Zpos xH
  | |- context [ Zpos xH ] => hide_Zpos xH

  (* atoms of type positive : we add a positivity condition (if not already there) *)
  | H : context [ Zpos ?a ] |- _ => 
        match goal with 
         | H' : Zpos a > 0 |- _ => hide_Zpos a
         | H' : Zpos' a > 0 |- _ => fail
         | _ => let H:= fresh "H" in assert (H:=Zgt_pos_0 a); hide_Zpos a
        end
  | |- context [ Zpos ?a ] => 
        match goal with 
         | H' : Zpos a > 0 |- _ => hide_Zpos a
         | H' : Zpos' a > 0 |- _ => fail
         | _ => let H:= fresh "H" in assert (H:=Zgt_pos_0 a); hide_Zpos a
        end
 end.

Ltac zify_positive := 
 repeat zify_positive_rel; repeat zify_positive_op; unfold Zpos',Zneg' in *.





(* IV) conversion from N to Z *) 

Definition Z_of_N' := Z_of_N.

Ltac hide_Z_of_N t := 
  let z := fresh "z" in set (z:=Z_of_N t) in *; 
  change Z_of_N with Z_of_N' in z; 
  unfold z in *; clear z.

Ltac zify_N_rel := 
 match goal with 
  (* I: equalities *)
  | H : (@eq N ?a ?b) |- _ => generalize (Z_of_N_eq _ _ H); clear H; intro H
  | |- (@eq N ?a ?b) => apply (Z_of_N_eq_rev a b)
  | H : context [ @eq N ?a ?b ] |- _ => rewrite (Z_of_N_eq_iff a b) in H
  | |- context [ @eq N ?a ?b ] =>       rewrite (Z_of_N_eq_iff a b)
  (* II: less than *)
  | H : (?a<?b)%N |- _ => generalize (Z_of_N_lt _ _ H); clear H; intro H
  | |- (?a<?b)%N => apply (Z_of_N_lt_rev a b)
  | H : context [ (?a<?b)%N ] |- _ => rewrite (Z_of_N_lt_iff a b) in H
  | |- context [ (?a<?b)%N ] =>       rewrite (Z_of_N_lt_iff a b)
  (* III: less or equal *)
  | H : (?a<=?b)%N |- _ => generalize (Z_of_N_le _ _ H); clear H; intro H
  | |- (?a<=?b)%N => apply (Z_of_N_le_rev a b)
  | H : context [ (?a<=?b)%N ] |- _ => rewrite (Z_of_N_le_iff a b) in H
  | |- context [ (?a<=?b)%N ] =>       rewrite (Z_of_N_le_iff a b)
  (* IV: greater than *)
  | H : (?a>?b)%N |- _ => generalize (Z_of_N_gt _ _ H); clear H; intro H
  | |- (?a>?b)%N => apply (Z_of_N_gt_rev a b)
  | H : context [ (?a>?b)%N ] |- _ => rewrite (Z_of_N_gt_iff a b) in H
  | |- context [ (?a>?b)%N ] =>       rewrite (Z_of_N_gt_iff a b)
  (* V: greater or equal *)
  | H : (?a>=?b)%N |- _ => generalize (Z_of_N_ge _ _ H); clear H; intro H
  | |- (?a>=?b)%N => apply (Z_of_N_ge_rev a b)
  | H : context [ (?a>=?b)%N ] |- _ => rewrite (Z_of_N_ge_iff a b) in H
  | |- context [ (?a>=?b)%N ] =>       rewrite (Z_of_N_ge_iff a b)
 end.
 
Ltac zify_N_op := 
 match goal with 
  (* misc type conversions: nat to positive *)
  | H : context [ Z_of_N (N_of_nat ?a) ] |- _ => rewrite (Z_of_N_of_nat a) in H
  | |- context [ Z_of_N (N_of_nat ?a) ] => rewrite (Z_of_N_of_nat a)
  | H : context [ Z_of_N (Zabs_N ?a) ] |- _ => rewrite (Z_of_N_abs a) in H
  | |- context [ Z_of_N (Zabs_N ?a) ] => rewrite (Z_of_N_abs a)
  | H : context [ Z_of_N (Npos ?a) ] |- _ => rewrite (Z_of_N_pos a) in H
  | |- context [ Z_of_N (Npos ?a) ] => rewrite (Z_of_N_pos a)
  | H : context [ Z_of_N N0 ] |- _ => change (Z_of_N N0) with Z0 in H
  | |- context [ Z_of_N N0 ] => change (Z_of_N N0) with Z0

  (* Nplus -> Zplus *)
  | H : context [ Z_of_N (Nplus ?a ?b) ] |- _ => rewrite (Z_of_N_plus a b) in H
  | |- context [ Z_of_N (Nplus ?a ?b) ] => rewrite (Z_of_N_plus a b)

  (* Nmin -> Zmin *)
  | H : context [ Z_of_N (Nmin ?a ?b) ] |- _ => rewrite (Z_of_N_min a b) in H
  | |- context [ Z_of_N (Nmin ?a ?b) ] => rewrite (Z_of_N_min a b)

  (* Nmax -> Zmax *)
  | H : context [ Z_of_N (Nmax ?a ?b) ] |- _ => rewrite (Z_of_N_max a b) in H
  | |- context [ Z_of_N (Nmax ?a ?b) ] => rewrite (Z_of_N_max a b)

  (* Nminus -> Zmax 0 (Zminus ... ...) *)
  | H : context [ Z_of_N (Nminus ?a ?b) ] |- _ => rewrite (Z_of_N_minus a b) in H
  | |- context [ Z_of_N (Nminus ?a ?b) ] => rewrite (Z_of_N_minus a b)

  (* Nsucc -> Zsucc *) 
  | H : context [ Z_of_N (Nsucc ?a) ] |- _ => rewrite (Z_of_N_succ a) in H
  | |- context [ Z_of_N (Nsucc ?a) ] => rewrite (Z_of_N_succ a)
 
  (* Nmult -> Zmult and a positivity hypothesis *)
  | H : context [ Z_of_N (Pmult ?a ?b) ] |- _ => 
        let H:= fresh "H" in 
        assert (H:=Z_of_N_le_0 (Pmult a b)); rewrite (Z_of_N_mult a b) in *
  | |- context [ Z_of_N  (Pmult ?a ?b) ] => 
        let H:= fresh "H" in 
        assert (H:=Z_of_N_le_0 (Pmult a b)); rewrite (Z_of_N_mult a b) in *

  (* atoms of type N : we add a positivity condition (if not already there) *) 
  | H : context [ Z_of_N ?a ] |- _ => 
        match goal with 
         | H' : 0 <= Z_of_N a |- _ => hide_Z_of_N a
         | H' : 0 <= Z_of_N' a |- _ => fail
         | _ => let H:= fresh "H" in assert (H:=Z_of_N_le_0 a); hide_Z_of_N a
        end
  | |- context [ Z_of_N ?a ] => 
        match goal with 
         | H' : 0 <= Z_of_N a |- _ => hide_Z_of_N a
         | H' : 0 <= Z_of_N' a |- _ => fail
         | _ => let H:= fresh "H" in assert (H:=Z_of_N_le_0 a); hide_Z_of_N a
        end
 end.

Ltac zify_N := repeat zify_N_rel; repeat zify_N_op; unfold Z_of_N' in *.



(** The complete Z-ification tactic *)

Ltac zify := 
 repeat progress (zify_nat; zify_positive; zify_N); zify_op.

