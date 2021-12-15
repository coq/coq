Require Import Coq.Arith.Arith Coq.Init.Wf.
Axiom proof_admitted : False.
Goal exists x y z : nat, Fix
                           Wf_nat.lt_wf
                           (fun _ => nat -> nat)
                           (fun x' f => match x' as x'0
                                              return match x'0 with
                                                       | 0 => True
                                                       | S x'' => x'' < x'
                                                     end
                                                     -> nat -> nat
                                        with
                                          | 0 => fun _ _ => 0
                                          | S x'' => f x''
                                        end
                                          (match x' with
                                             | 0 => I
                                             | S x'' => (Nat.lt_succ_diag_r _)
                                           end))
                           z
                           y
                         = 0.
Proof.
  do 3 (eexists; [ shelve.. | ]).
  match goal with |- ?G => let G' := (eval lazy in G) in change G with G' end.
  case proof_admitted.
  Unshelve.
  all:constructor.
Defined.
