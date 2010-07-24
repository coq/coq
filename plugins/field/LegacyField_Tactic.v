(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Import List.
Require Import LegacyRing.
Require Export LegacyField_Compl.
Require Export LegacyField_Theory.

(**** Interpretation A --> ExprA ****)

Ltac get_component a s := eval cbv beta iota delta [a] in (a s).

Ltac body_of s := eval cbv beta iota delta [s] in s.

Ltac mem_assoc var lvar :=
  match constr:lvar with
  | nil => constr:false
  | ?X1 :: ?X2 =>
      match constr:(X1 = var) with
      | (?X1 = ?X1) => constr:true
      | _ => mem_assoc var X2
      end
  end.

Ltac number lvar :=
  let rec number_aux lvar cpt :=
    match constr:lvar with
    | (@nil ?X1) => constr:(@nil (prod X1 nat))
    | ?X2 :: ?X3 =>
        let l2 := number_aux X3 (S cpt) in
        constr:((X2,cpt) :: l2)
    end
  in number_aux lvar 0.

Ltac build_varlist FT trm :=
  let rec seek_var lvar trm :=
    let AT := get_component A FT
    with AzeroT := get_component Azero FT
    with AoneT := get_component Aone FT
    with AplusT := get_component Aplus FT
    with AmultT := get_component Amult FT
    with AoppT := get_component Aopp FT
    with AinvT := get_component Ainv FT in
    match constr:trm with
    | AzeroT => lvar
    | AoneT => lvar
    | (AplusT ?X1 ?X2) =>
        let l1 := seek_var lvar X1 in
        seek_var l1 X2
    | (AmultT ?X1 ?X2) =>
        let l1 := seek_var lvar X1 in
        seek_var l1 X2
    | (AoppT ?X1) => seek_var lvar X1
    | (AinvT ?X1) => seek_var lvar X1
    | ?X1 =>
        let res := mem_assoc X1 lvar in
        match constr:res with
        | true => lvar
        | false => constr:(X1 :: lvar)
        end
    end in
  let AT := get_component A FT in
  let lvar := seek_var (@nil AT) trm in
  number lvar.

Ltac assoc elt lst :=
  match constr:lst with
  | nil => fail
  | (?X1,?X2) :: ?X3 =>
      match constr:(elt = X1) with
      | (?X1 = ?X1) => constr:X2
      | _ => assoc elt X3
      end
  end.

Ltac interp_A FT lvar trm :=
  let AT := get_component A FT
  with AzeroT := get_component Azero FT
  with AoneT := get_component Aone FT
  with AplusT := get_component Aplus FT
  with AmultT := get_component Amult FT
  with AoppT := get_component Aopp FT
  with AinvT := get_component Ainv FT in
  match constr:trm with
  | AzeroT => constr:EAzero
  | AoneT => constr:EAone
  | (AplusT ?X1 ?X2) =>
      let e1 := interp_A FT lvar X1 with e2 := interp_A FT lvar X2 in
      constr:(EAplus e1 e2)
  | (AmultT ?X1 ?X2) =>
      let e1 := interp_A FT lvar X1 with e2 := interp_A FT lvar X2 in
      constr:(EAmult e1 e2)
  | (AoppT ?X1) =>
      let e := interp_A FT lvar X1 in
      constr:(EAopp e)
  | (AinvT ?X1) => let e := interp_A FT lvar X1 in
                   constr:(EAinv e)
  | ?X1 => let idx := assoc X1 lvar in
           constr:(EAvar idx)
  end.

(************************)
(*    Simplification    *)
(************************)

(**** Generation of the multiplier ****)

Ltac remove e l :=
  match constr:l with
  | nil => l
  | e :: ?X2 => constr:X2
  | ?X2 :: ?X3 => let nl := remove e X3 in constr:(X2 :: nl)
  end.

Ltac union l1 l2 :=
  match constr:l1 with
  | nil => l2
  | ?X2 :: ?X3 =>
      let nl2 := remove X2 l2 in
      let nl := union X3 nl2 in
      constr:(X2 :: nl)
  end.

Ltac raw_give_mult trm :=
  match constr:trm with
  | (EAinv ?X1) => constr:(X1 :: nil)
  | (EAopp ?X1) => raw_give_mult X1
  | (EAplus ?X1 ?X2) =>
      let l1 := raw_give_mult X1 with l2 := raw_give_mult X2 in
      union l1 l2
  | (EAmult ?X1 ?X2) =>
      let l1 := raw_give_mult X1 with l2 := raw_give_mult X2 in
      eval compute in (app l1 l2)
  | _ => constr:(@nil ExprA)
  end.

Ltac give_mult trm :=
  let ltrm := raw_give_mult trm in
  constr:(mult_of_list ltrm).

(**** Associativity ****)

Ltac apply_assoc FT lvar trm :=
  let t := eval compute in (assoc trm) in
  match constr:(t = trm) with
  | (?X1 = ?X1) => idtac
  | _ =>
      rewrite <- (assoc_correct FT trm); change (assoc trm) with t in |- *
  end.

(**** Distribution *****)

Ltac apply_distrib FT lvar trm :=
  let t := eval compute in (distrib trm) in
  match constr:(t = trm) with
  | (?X1 = ?X1) => idtac
  | _ =>
      rewrite <- (distrib_correct FT trm);
       change (distrib trm) with t in |- *
  end.

(**** Multiplication by the inverse product ****)

Ltac grep_mult := match goal with
                  | id:(interp_ExprA _ _ _ <> _) |- _ => id
                  end.

Ltac weak_reduce :=
  match goal with
  |  |- context [(interp_ExprA ?X1 ?X2 _)] =>
      cbv beta iota zeta
       delta [interp_ExprA assoc_2nd eq_nat_dec mult_of_list X1 X2 A Azero
             Aone Aplus Amult Aopp Ainv] in |- *
  end.

Ltac multiply mul :=
  match goal with
  |  |- (interp_ExprA ?FT ?X2 ?X3 = interp_ExprA ?FT ?X2 ?X4) =>
      let AzeroT := get_component Azero FT in
      cut (interp_ExprA FT X2 mul <> AzeroT);
       [ intro; (let id := grep_mult in apply (mult_eq FT X3 X4 mul X2 id))
       | weak_reduce;
          (let AoneT := get_component Aone ltac:(body_of FT)
           with AmultT := get_component Amult ltac:(body_of FT) in
           try
             match goal with
             |  |- context [(AmultT _ AoneT)] => rewrite (AmultT_1r FT)
             end; clear FT X2) ]
  end.

Ltac apply_multiply FT lvar trm :=
  let t := eval compute in (multiply trm) in
  match constr:(t = trm) with
  | (?X1 = ?X1) => idtac
  | _ =>
      rewrite <- (multiply_correct FT trm);
       change (multiply trm) with t in |- *
  end.

(**** Permutations and simplification ****)

Ltac apply_inverse mul FT lvar trm :=
  let t := eval compute in (inverse_simplif mul trm) in
  match constr:(t = trm) with
  | (?X1 = ?X1) => idtac
  | _ =>
      rewrite <- (inverse_correct FT trm mul);
       [ change (inverse_simplif mul trm) with t in |- * | assumption ]
  end.
(**** Inverse test ****)

Ltac strong_fail tac := first [ tac | fail 2 ].

Ltac inverse_test_aux FT trm :=
  let AplusT := get_component Aplus FT
  with AmultT := get_component Amult FT
  with AoppT := get_component Aopp FT
  with AinvT := get_component Ainv FT in
  match constr:trm with
  | (AinvT _) => fail 1
  | (AoppT ?X1) =>
      strong_fail ltac:(inverse_test_aux FT X1; idtac)
  | (AplusT ?X1 ?X2) =>
      strong_fail ltac:(inverse_test_aux FT X1; inverse_test_aux FT X2)
  | (AmultT ?X1 ?X2) =>
      strong_fail ltac:(inverse_test_aux FT X1; inverse_test_aux FT X2)
  | _ => idtac
  end.

Ltac inverse_test FT :=
  let AplusT := get_component Aplus FT in
  match goal with
  |  |- (?X1 = ?X2) => inverse_test_aux FT (AplusT X1 X2)
  end.

(**** Field itself ****)

Ltac apply_simplif sfun :=
  match goal with
  |  |- (interp_ExprA ?X1 ?X2 ?X3 = interp_ExprA _ _ _) =>
  sfun X1 X2 X3
  end;
   match goal with
   |  |- (interp_ExprA _ _ _ = interp_ExprA ?X1 ?X2 ?X3) =>
   sfun X1 X2 X3
   end.

Ltac unfolds FT :=
  match get_component Aminus FT with
  | Some ?X1 => unfold X1 in |- *
  | _ => idtac
  end;
  match get_component Adiv FT with
  | Some ?X1 => unfold X1 in |- *
  | _ => idtac
  end.

Ltac reduce FT :=
  let AzeroT := get_component Azero FT
  with AoneT := get_component Aone FT
  with AplusT := get_component Aplus FT
  with AmultT := get_component Amult FT
  with AoppT := get_component Aopp FT
  with AinvT := get_component Ainv FT in
  (cbv beta iota zeta delta -[AzeroT AoneT AplusT AmultT AoppT AinvT] in |- * ||
     compute in |- *).

Ltac field_gen_aux FT :=
  let AplusT := get_component Aplus FT in
  match goal with
  |  |- (?X1 = ?X2) =>
      let lvar := build_varlist FT (AplusT X1 X2) in
      let trm1 := interp_A FT lvar X1 with trm2 := interp_A FT lvar X2 in
      let mul := give_mult (EAplus trm1 trm2) in
      cut
        (let ft := FT in
         let vm := lvar in interp_ExprA ft vm trm1 = interp_ExprA ft vm trm2);
        [ compute in |- *; auto
        | intros ft vm; apply_simplif apply_distrib;
           apply_simplif apply_assoc; multiply mul;
           [ apply_simplif apply_multiply;
              apply_simplif ltac:(apply_inverse mul);
              (let id := grep_mult in
               clear id; weak_reduce; clear ft vm; first
              [ inverse_test FT; legacy ring | field_gen_aux FT ])
           | idtac ] ]
  end.

Ltac field_gen FT :=
  unfolds FT; (inverse_test FT; legacy ring) || field_gen_aux FT.

(*****************************)
(*    Term Simplification    *)
(*****************************)

(**** Minus and division expansions ****)

Ltac init_exp FT trm :=
  let e :=
   (match get_component Aminus FT with
    | Some ?X1 => eval cbv beta delta [X1] in trm
    | _ => trm
    end) in
  match get_component Adiv FT with
  | Some ?X1 => eval cbv beta delta [X1] in e
  | _ => e
  end.

(**** Inverses simplification ****)

Ltac simpl_inv trm :=
  match constr:trm with
  | (EAplus ?X1 ?X2) =>
      let e1 := simpl_inv X1 with e2 := simpl_inv X2 in
      constr:(EAplus e1 e2)
  | (EAmult ?X1 ?X2) =>
      let e1 := simpl_inv X1 with e2 := simpl_inv X2 in
      constr:(EAmult e1 e2)
  | (EAopp ?X1) => let e := simpl_inv X1 in
                   constr:(EAopp e)
  | (EAinv ?X1) => SimplInvAux X1
  | ?X1 => constr:X1
  end
 with SimplInvAux trm :=
  match constr:trm with
  | (EAinv ?X1) => simpl_inv X1
  | (EAmult ?X1 ?X2) =>
      let e1 := simpl_inv (EAinv X1) with e2 := simpl_inv (EAinv X2) in
      constr:(EAmult e1 e2)
  | ?X1 => let e := simpl_inv X1 in
           constr:(EAinv e)
  end.

(**** Monom simplification ****)

Ltac map_tactic fcn lst :=
  match constr:lst with
  | nil => lst
  | ?X2 :: ?X3 =>
      let r := fcn X2 with t := map_tactic fcn X3 in
      constr:(r :: t)
  end.

Ltac build_monom_aux lst trm :=
  match constr:lst with
  | nil => eval compute in (assoc trm)
  | ?X1 :: ?X2 => build_monom_aux X2 (EAmult trm X1)
  end.

Ltac build_monom lnum lden :=
  let ildn := map_tactic ltac:(fun e => constr:(EAinv e)) lden in
  let ltot := eval compute in (app lnum ildn) in
  let trm := build_monom_aux ltot EAone in
  match constr:trm with
  | (EAmult _ ?X1) => constr:X1
  | ?X1 => constr:X1
  end.

Ltac simpl_monom_aux lnum lden trm :=
  match constr:trm with
  | (EAmult (EAinv ?X1) ?X2) =>
      let mma := mem_assoc X1 lnum in
      match constr:mma with
      | true =>
          let newlnum := remove X1 lnum in
          simpl_monom_aux newlnum lden X2
      | false => simpl_monom_aux lnum (X1 :: lden) X2
      end
  | (EAmult ?X1 ?X2) =>
      let mma := mem_assoc X1 lden in
      match constr:mma with
      | true =>
          let newlden := remove X1 lden in
          simpl_monom_aux lnum newlden X2
      | false => simpl_monom_aux (X1 :: lnum) lden X2
      end
  | (EAinv ?X1) =>
      let mma := mem_assoc X1 lnum in
      match constr:mma with
      | true =>
          let newlnum := remove X1 lnum in
          build_monom newlnum lden
      | false => build_monom lnum (X1 :: lden)
      end
  | ?X1 =>
      let mma := mem_assoc X1 lden in
      match constr:mma with
      | true =>
          let newlden := remove X1 lden in
          build_monom lnum newlden
      | false => build_monom (X1 :: lnum) lden
      end
  end.

Ltac simpl_monom trm := simpl_monom_aux (@nil ExprA) (@nil ExprA) trm.

Ltac simpl_all_monomials trm :=
  match constr:trm with
  | (EAplus ?X1 ?X2) =>
      let e1 := simpl_monom X1 with e2 := simpl_all_monomials X2 in
      constr:(EAplus e1 e2)
  | ?X1 => simpl_monom X1
  end.

(**** Associativity and distribution ****)

Ltac assoc_distrib trm := eval compute in (assoc (distrib trm)).

(**** The tactic Field_Term ****)

Ltac eval_weak_reduce trm :=
  eval
   cbv beta iota zeta
    delta [interp_ExprA assoc_2nd eq_nat_dec mult_of_list A Azero Aone Aplus
          Amult Aopp Ainv] in trm.

Ltac field_term FT exp :=
  let newexp := init_exp FT exp in
  let lvar := build_varlist FT newexp in
  let trm := interp_A FT lvar newexp in
  let tma := eval compute in (assoc trm) in
  let tsmp :=
   simpl_all_monomials
    ltac:(assoc_distrib ltac:(simpl_all_monomials ltac:(simpl_inv tma))) in
  let trep := eval_weak_reduce (interp_ExprA FT lvar tsmp) in
  (replace exp with trep; [ legacy ring trep | field_gen FT ]).
