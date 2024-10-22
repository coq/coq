(** Deprecated alias for Coqlib *)

include Rocqlib

open Names

type coq_sigma_data = rocq_sigma_data = {
  proj1 : GlobRef.t;
  proj2 : GlobRef.t;
  elim  : GlobRef.t;
  intro : GlobRef.t;
  typ   : GlobRef.t }

type coq_eq_data = rocq_eq_data = {
  eq   : GlobRef.t;
  ind  : GlobRef.t;
  refl : GlobRef.t;
  sym  : GlobRef.t;
  trans: GlobRef.t;
  congr: GlobRef.t }

let build_coq_eq_data = build_rocq_eq_data
let build_coq_identity_data = build_rocq_identity_data
let build_coq_jmeq_data = build_rocq_jmeq_data
