open Names
open Cbytecodes

type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of constant Univ.puniverses

type patch = reloc_info * int

(* A virer *)
val subst_patch : Mod_subst.substitution -> patch -> patch

type emitcodes

val copy : emitcodes -> emitcodes

val length : emitcodes -> int

val patch_int : emitcodes -> (*pos*)int -> int -> unit

type to_patch = emitcodes * (patch list) * fv

val subst_to_patch : Mod_subst.substitution -> to_patch -> to_patch

type body_code =
  | BCdefined of to_patch
  | BCallias of constant Univ.puniverses
  | BCconstant


type to_patch_substituted

val from_val : body_code -> to_patch_substituted

val force : to_patch_substituted -> body_code

val subst_to_patch_subst : Mod_subst.substitution -> to_patch_substituted -> to_patch_substituted

val repr_body_code :
  to_patch_substituted -> Mod_subst.substitution list option * body_code

val to_memory : bytecodes * bytecodes * fv -> to_patch
               (** init code, fun code, fv *)
