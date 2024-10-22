(** Deprecated alias for Rocqlib *)

[@@@ocaml.deprecated "(9.0) Use Rocqlib"]
include module type of struct include Rocqlib end

open Names
open Util

type coq_sigma_data = rocq_sigma_data = {
  proj1 : GlobRef.t;
  proj2 : GlobRef.t;
  elim  : GlobRef.t;
  intro : GlobRef.t;
  typ   : GlobRef.t } [@@ocaml.deprecated "(9.0) Use Rocqlib.rocq_sigma_data"]

type coq_eq_data = rocq_eq_data = {
  eq   : GlobRef.t;
  ind  : GlobRef.t;
  refl : GlobRef.t;
  sym  : GlobRef.t;
  trans: GlobRef.t;
  congr: GlobRef.t } [@@ocaml.deprecated "(9.0) Use Rocqlib.rocq_eq_data"]

val build_coq_eq_data : rocq_eq_data delayed [@@ocaml.deprecated "(9.0) Use Rocqlib.build_rocq_eq_data"]
val build_coq_identity_data : rocq_eq_data delayed [@@ocaml.deprecated "(9.0) Use Rocqlib.build_rocq_identity_data"]
val build_coq_jmeq_data : rocq_eq_data delayed [@@ocaml.deprecated "(9.0) Use Rocqlib.build_rocq_jmeq_data"]
