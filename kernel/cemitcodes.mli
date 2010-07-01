open Names
open Cbytecodes

type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of constant
  | Reloc_caml_prim of Native.caml_prim

type patch = reloc_info * int

(* A virer *)
val subst_patch : Mod_subst.substitution -> patch -> patch

type emitcodes

val length : emitcodes -> int

val patch_int : emitcodes -> (*pos*)int -> int -> unit

type to_patch = emitcodes * (patch array) * fv

val subst_to_patch : Mod_subst.substitution -> to_patch -> to_patch

type body_code =
  | BCdefined of bool*to_patch
  | BCallias of constant
  | BCconstant


type to_patch_substituted

val from_val : body_code -> to_patch_substituted

val force : to_patch_substituted -> body_code

val is_boxed : to_patch_substituted -> bool

val subst_to_patch_subst : Mod_subst.substitution -> to_patch_substituted -> to_patch_substituted

val to_memory : bytecodes * bytecodes * fv -> to_patch
               (** init code, fun code, fv *)
