
open Util
open Pp
open Term
open Tacmach
open Fol

type prover = Simplify | CVCLite | Harvey

let dp prover gl =
  let concl = pf_concl gl in
  if not (is_Prop (pf_type_of gl concl)) then error "not a proposition";
  error "not yet implemented"

let simplify = dp Simplify
let cvc_lite = dp CVCLite
let harvey = dp Harvey

