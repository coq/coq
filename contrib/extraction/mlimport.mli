
(*i $Id$ i*)

open Names
open Term

val add_ml_import : global_reference -> identifier -> unit
val is_ml_import : global_reference -> bool
val find_ml_import : global_reference -> identifier

val add_ml_extract : global_reference -> identifier -> unit
val find_ml_extract : global_reference -> identifier
val is_ml_extract : global_reference -> bool

(*
val list0n : int -> int list
val next_global_ident : Names.identifier -> Names.identifier
val ml_import_tab : (Term.sorts Term.oper, Names.identifier) Hashtabl.t
val mL_INDUCTIVES : Names.section_path list ref
val add_ml_inductive_import : Names.section_path -> unit
val sp_is_ml_import : Names.section_path -> bool
val sp_prod : Names.section_path
val sp_is_ml_import_or_prod : Names.section_path -> bool
val inMLImport : Term.sorts Term.oper * Names.identifier -> Libobject.obj
val outMLImport : Libobject.obj -> Term.sorts Term.oper * Names.identifier
val ml_extract_tab : (Term.sorts Term.oper, Names.identifier) Hashtabl.t
val sp_is_ml_extract : Names.section_path -> bool
val inMLExtract : Term.sorts Term.oper * Names.identifier -> Libobject.obj
val outMLExtract : Libobject.obj -> Term.sorts Term.oper * Names.identifier
val is_import_or_extract : Names.section_path -> bool
val freeze :
  unit ->
  (Term.sorts Term.oper, Names.identifier) Hashtabl.frozen_t *
  Names.section_path list *
  (Term.sorts Term.oper, Names.identifier) Hashtabl.frozen_t
val unfreeze :
  (Term.sorts Term.oper, Names.identifier) Hashtabl.frozen_t *
  Names.section_path list *
  (Term.sorts Term.oper, Names.identifier) Hashtabl.frozen_t -> unit
val whd_fwify : 'a Term.oper Generic.term -> 'a Term.oper Generic.term
val fwify : Reduction.reduction_function
val fwsp_of_id : Names.identifier -> Names.section_path
val make_fw_parameter_body :
  Term.type_judgement Names.signature * Term.type_judgement ->
  Constrtypes.constant_body
val fw_infexecute_parameter :
  Term.context ->
  Names.identifier ->
  Term.constr ->
  Impuniv.universes * (Names.path_kind * Constrtypes.constant_body) list
val fw_machine_parameter :
  Term.context -> Names.identifier * Term.constr -> unit
val fw_parameter : Names.identifier -> CoqAst.t -> unit
val ml_import : Names.identifier -> Names.identifier -> CoqAst.t -> unit
val id_of_varg : Vernacinterp.vernac_arg -> Names.identifier
val not_an_axiom : Names.identifier -> 'a
val not_have_type :
  Term.environment ->
  Constrtypes.constant_body -> Constrtypes.constant_body -> 'a
val fw_infexecute_constant :
  Term.context ->
  Names.identifier ->
  Term.constr ->
  Impuniv.universes * (Names.path_kind * Constrtypes.constant_body) list
val fw_link : Names.identifier -> CoqAst.t -> unit
val fw_machine_minductive :
  Term.context ->
  int ->
  (Names.identifier * Names.name * Term.type_judgement * Term.constr *
   Names.identifier array)
  array -> bool -> unit
val fw_fconstruct :
  'a Evd.evar_map -> Term.context -> CoqAst.t -> Term.type_judgement
val fw_build_mutual :
  (Names.identifier * CoqAst.t) list ->
  (Names.identifier * CoqAst.t * (Names.identifier * CoqAst.t) list) list ->
  bool -> unit
val not_same_number_types : unit -> 'a
val not_same_number_constructors : Names.identifier * Names.identifier -> 'a
val ml_import_inductive :
  (Names.identifier * Names.identifier list) list ->
  (Names.identifier * CoqAst.t) list ->
  (Names.identifier * CoqAst.t * (Names.identifier * CoqAst.t) list) list ->
  bool -> unit
val extract_constant : Names.identifier -> Names.identifier -> unit
val extract_inductive :
  Names.identifier -> Names.identifier * Names.identifier list -> unit
val fprint_recipe : Constrtypes.recipe ref option -> Pp.std_ppcmds
val fprint_name : Names.identifier -> Pp.std_ppcmds
*)
