
open Util
open Pp
open Term
open Tacmach
open Fol

let simplify gl =
  let concl = pf_concl gl in
  if not (is_Prop (pf_type_of gl concl)) then error "not a proposition";
  msgnl (str "nb of hyps = " ++ int (List.length (pf_hyps gl)));
  pp_flush ();
  error "not yet implemented"
