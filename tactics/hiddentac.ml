
(* $Id$ *)

open Term
open Proof_type
open Tacmach
open Tacentries

let h_clear ids         = v_clear  [(Clause ids)]
let h_move dep id1 id2  = 
 (if dep then v_move else v_move_dep) [Identifier id1;Identifier id2]
let h_contradiction     = v_contradiction []
let h_reflexivity       = v_reflexivity   []
let h_symmetry          = v_symmetry      []
let h_assumption        = v_assumption    []
let h_absurd c          = v_absurd [(Constr c)]
let h_exact  c          = v_exact  [(Constr c)]
let h_one_constructor i = v_constructor [(Integer i)]
let h_any_constructor   = v_constructor []
let h_transitivity c    = v_transitivity [(Constr c)]
let h_simplest_left     = v_left [(Cbindings [])]
let h_simplest_right    = v_right [(Cbindings [])]
let h_split     c       = v_split [(Constr c);(Cbindings [])]
let h_apply c s         = v_apply  [(Constr c);(Cbindings s)]
let h_simplest_apply c  = v_apply  [(Constr c);(Cbindings [])]
let h_cut      c        = v_cut [(Constr c)]
let h_simplest_elim c   = v_elim [(Constr c);(Cbindings [])]
let h_elimType     c    = v_elimType [(Constr c)]
let h_inductionInt  i   = v_induction[(Integer i)]
let h_inductionId   id  = v_induction[(Identifier id)]
let h_simplest_case   c = v_case [(Constr c);(Cbindings [])]
let h_caseType        c = v_caseType [(Constr c)]
let h_destructInt  i    = v_destruct [(Integer i)]
let h_destructId   id   = v_destruct [(Identifier id)]



