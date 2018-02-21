(* record of Printing options *)

type t = {
    printing_allow_match_default_clause : bool;
    printing_coercions : bool;
    printing_compact_contexts : bool;
    printing_existential_instances : bool;
    printing_factorizable_match_patterns : bool;
    printing_implicit: bool;
    printing_implicit_defensive : bool;
    printing_let_binder_types : bool;
    printing_matching : bool;
    printing_notations : bool;
    printing_primitive_projection_compatibility : bool;
    printing_primitive_projection_parameters : bool;
    printing_projections : bool;
    printing_records : bool;
    printing_synth : bool;
    printing_universes : bool;
    printing_wildcard : bool;
  }

let default_options : t = {
    printing_allow_match_default_clause = true;
    printing_coercions = false;
    printing_compact_contexts = false;
    printing_existential_instances = false;
    printing_factorizable_match_patterns = true;
    printing_implicit = false;
    printing_implicit_defensive = true;
    printing_let_binder_types = false;
    printing_matching = true;
    printing_notations = true;
    printing_primitive_projection_compatibility = false;
    printing_primitive_projection_parameters = false;
    printing_projections = false;
    printing_records = true;
    printing_synth = true;
    printing_universes = false;
    printing_wildcard = true;
  }

let all_options : t = {
    printing_allow_match_default_clause = false;
    printing_coercions = true;
    printing_compact_contexts = true;
    printing_existential_instances = true;
    printing_factorizable_match_patterns = false;
    printing_implicit = true;
    printing_implicit_defensive = true;
    printing_let_binder_types = true;
    printing_matching = false;
    printing_notations = false;
    printing_primitive_projection_compatibility = true;
    printing_primitive_projection_parameters = true;
    printing_projections = false;
    printing_records = false;
    printing_synth = false;
    printing_universes = true;
    printing_wildcard = false;
  }

(* use negation of corresponding fields in all_options *)
let sugared_options : t = {
    printing_allow_match_default_clause = not all_options.printing_allow_match_default_clause;
    printing_coercions = not all_options.printing_coercions;
    printing_compact_contexts = not all_options.printing_compact_contexts;
    printing_existential_instances = not all_options.printing_existential_instances;
    printing_factorizable_match_patterns = not all_options.printing_factorizable_match_patterns;
    printing_implicit = not all_options.printing_implicit;
    printing_implicit_defensive = not all_options.printing_implicit_defensive;
    printing_let_binder_types = not all_options.printing_let_binder_types;
    printing_matching = not all_options.printing_matching;
    printing_notations = not all_options.printing_notations;
    printing_primitive_projection_compatibility = not all_options.printing_primitive_projection_compatibility;
    printing_primitive_projection_parameters = not all_options.printing_primitive_projection_parameters;
    printing_projections = not all_options.printing_projections;
    printing_records = not all_options.printing_records;
    printing_synth = not all_options.printing_synth;
    printing_universes = not all_options.printing_universes;
    printing_wildcard = not all_options.printing_wildcard;
  }

let current_options = Summary.ref ~name:"printing options" default_options

let get_current_options () = !current_options
let set_current_options opts = current_options := opts

let saved_options = Summary.ref ~name:"saved printing options" None

let get_saved_options () = !saved_options
let set_saved_options opts = saved_options := opts

(* given a print options record, get list of option names and their values,
   used when setting options locally
   somewhat redundant with the option declarations, so a bit fragile
 *)
let options_by_name_value opts =
  [ (["Printing";"Allow";"Match";"Default";"Clause"],opts.printing_allow_match_default_clause);
    (["Printing";"Coercions"],opts.printing_coercions);
    (["Printing";"Compact";"Contexts"],opts.printing_compact_contexts);
    (["Printing";"Existential";"Instances"],opts.printing_existential_instances);
    (["Printing";"Factorizable";"Match";"Patterns"],opts.printing_factorizable_match_patterns);
    (["Printing";"Implicit"],opts.printing_implicit);
    (["Printing";"Implicit";"Defensive"],opts.printing_implicit_defensive);
    (["Printing";"Let";"Binder";"Types"],opts.printing_let_binder_types);
    (["Printing";"Matching"],opts.printing_matching);
    (["Printing";"Notations"],opts.printing_notations);
    (["Printing";"Primitive";"Projection";"Compatibility"],opts.printing_primitive_projection_compatibility);
    (["Printing";"Primitive";"Projection";"Parameters"],opts.printing_primitive_projection_parameters);
    (["Printing";"Projections"],opts.printing_projections);
    (["Printing";"Records"],opts.printing_records);
    (["Printing";"Synth"],opts.printing_synth);
    (["Printing";"Universes"],opts.printing_universes);
    (["Printing";"Wildcard"],opts.printing_wildcard);
  ]

let all_names_values = options_by_name_value all_options
let sugared_names_values = options_by_name_value sugared_options
let default_names_values = options_by_name_value default_options

let mk_printing_local opts_vals =
  List.iter
    (fun (opt,b) ->
      Goptions.set_bool_option_value_gen ~locality:Goptions.OptLocal opt b)
    opts_vals

let set_printing_all_global () = set_current_options all_options
let set_printing_all_local () = mk_printing_local all_names_values

let set_printing_all ~local =
  set_saved_options (Some (get_current_options ()));
  if local then
    set_printing_all_local ()
  else
    set_printing_all_global ()

let noop_unset_printing_all_warning =
  CWarnings.create ~name:"noop-unset-printing-all" ~category:"vernacular"
    (fun () -> Pp.str("Unset Printing All here has no effect."))

let unset_printing_all () =
  match get_saved_options () with
  | Some opts ->
     set_current_options opts;
     set_saved_options None
  | None -> noop_unset_printing_all_warning ()

let set_printing_sugared_global () = set_current_options sugared_options
let set_printing_sugared_local () = mk_printing_local sugared_names_values

let set_printing_sugared ~local =
  if local then
    set_printing_sugared_local ()
  else
    set_printing_sugared_global ()

let set_printing_defaults_global () = set_current_options default_options
let set_printing_defaults_local () = mk_printing_local default_names_values

let set_printing_defaults ~local =
  if local then
    set_printing_defaults_local ()
  else
    set_printing_defaults_global ()

(* getters/setters for Printing options, grouped by system component *)

(* getters/setters used in Constrextern *)
let printing_coercions () = !current_options.printing_coercions
let set_printing_coercions b =
  current_options := { !current_options with printing_coercions = b }

let printing_notations () = !current_options.printing_notations
let set_printing_notations b =
  current_options := { !current_options with printing_notations = b }

let printing_records () = !current_options.printing_records
let set_printing_records b =
  current_options := { !current_options with printing_records = b }

let printing_implicit () = !current_options.printing_implicit
let set_printing_implicit b =
  current_options := { !current_options with printing_implicit = b }

let printing_implicit_defensive () = !current_options.printing_implicit_defensive
let set_printing_implicit_defensive b =
  current_options := { !current_options with printing_implicit_defensive = b }

let printing_projections () = !current_options.printing_projections
let set_printing_projections b =
  current_options := { !current_options with printing_projections = b }

(* getters/setters used in Detyping *)
let printing_allow_match_default_clause () = !current_options.printing_allow_match_default_clause
let set_printing_allow_match_default_clause b =
  current_options := { !current_options with printing_allow_match_default_clause = b }

let printing_existential_instances () = !current_options.printing_existential_instances
let set_printing_existential_instances b =
  current_options := { !current_options with printing_existential_instances = b }

let printing_factorizable_match_patterns () = !current_options.printing_factorizable_match_patterns
let set_printing_factorizable_match_patterns b =
  current_options := { !current_options with printing_factorizable_match_patterns = b }

let printing_let_binder_types () = !current_options.printing_let_binder_types
let set_printing_let_binder_types b =
  current_options := { !current_options with printing_let_binder_types = b }

let printing_matching () = !current_options.printing_matching
let set_printing_matching b =
  current_options := { !current_options with printing_matching = b }

let printing_primitive_projection_compatibility () = !current_options.printing_primitive_projection_compatibility
let set_printing_primitive_projection_compatibility b =
  current_options := { !current_options with printing_primitive_projection_compatibility = b }

let printing_primitive_projection_parameters () = !current_options.printing_primitive_projection_parameters
let set_printing_primitive_projection_parameters b =
  current_options := { !current_options with printing_primitive_projection_parameters = b }

let printing_synth () = !current_options.printing_synth
let set_printing_synth b =
  current_options := { !current_options with printing_synth = b }

let printing_wildcard () = !current_options.printing_wildcard
let set_printing_wildcard b =
  current_options := { !current_options with printing_wildcard = b }

(* getters/setters used in Printing *)
let printing_compact_contexts () = !current_options.printing_compact_contexts
let set_printing_compact_contexts b =
  current_options := { !current_options with printing_compact_contexts = b }

(* getters/setters used in Constrextern/Detyping/Printer (+ Funind plugin) *)
let printing_universes () = !current_options.printing_universes
let set_printing_universes b =
  current_options := { !current_options with printing_universes = b }

(* set printing option, run `f x`, restore options *)
(* can't use Flags.with_option, individual printing options are not references *)
let with_printing_option set_opt f x =
  let saved_opts = get_current_options () in
  let _ = set_current_options (set_opt saved_opts) in
  try
    let res = f x in
    let _ = set_current_options saved_opts in
    res
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    let _ = set_current_options saved_opts in
    Exninfo.iraise reraise
