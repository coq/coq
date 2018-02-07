(* record of Printing options *)

type t = {
    printing_allow_match_default_clause : bool;
    printing_coercions : bool;
    printing_compact_contexts : bool;
    printing_existential_instances : bool;
    printing_factorizable_match_patterns : bool;
    printing_implicit: bool;
    printing_implicit_defensive : bool;
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

let set_printing_all () = current_options := all_options
let set_printing_sugared () = current_options := sugared_options
let set_printing_defaults () = current_options := default_options

let printing_all () = (!current_options = all_options)

let printing_allow_match_default_clause () = !current_options.printing_allow_match_default_clause
let printing_coercions () = !current_options.printing_coercions
let printing_compact_contexts () = !current_options.printing_compact_contexts
let printing_existential_instances () = !current_options.printing_existential_instances
let printing_factorizable_match_patterns () = !current_options.printing_factorizable_match_patterns
let printing_implicit () = !current_options.printing_implicit
let printing_implicit_defensive () = !current_options.printing_implicit_defensive
let printing_matching () = !current_options.printing_matching
let printing_notations () = !current_options.printing_notations
let printing_primitive_projection_compatibility () = !current_options.printing_primitive_projection_compatibility
let printing_primitive_projection_parameters () = !current_options.printing_primitive_projection_parameters
let printing_projections () = !current_options.printing_projections
let printing_records () = !current_options.printing_records
let printing_synth () = !current_options.printing_synth
let printing_universes () = !current_options.printing_universes
let printing_wildcard () = !current_options.printing_wildcard

let set_printing_allow_match_default_clause b =
  current_options := { !current_options with printing_allow_match_default_clause = b }
let set_printing_coercions b =
  current_options := { !current_options with printing_coercions = b }
let set_printing_compact_contexts b =
  current_options := { !current_options with printing_compact_contexts = b }
let set_printing_existential_instances b =
  current_options := { !current_options with printing_existential_instances = b }
let set_printing_factorizable_match_patterns b =
  current_options := { !current_options with printing_factorizable_match_patterns = b }
let set_printing_implicit b =
  current_options := { !current_options with printing_implicit = b }
let set_printing_implicit_defensive b =
  current_options := { !current_options with printing_implicit_defensive = b }
let set_printing_matching b =
  current_options := { !current_options with printing_matching = b }
let set_printing_notations b =
  current_options := { !current_options with printing_notations = b }
let set_printing_primitive_projection_compatibility b =
  current_options := { !current_options with printing_primitive_projection_compatibility = b }
let set_printing_primitive_projection_parameters b =
  current_options := { !current_options with printing_primitive_projection_parameters = b }
let set_printing_projections b =
  current_options := { !current_options with printing_projections = b }
let set_printing_records b =
  current_options := { !current_options with printing_records = b }
let set_printing_synth b =
  current_options := { !current_options with printing_synth = b }
let set_printing_universes b =
  current_options := { !current_options with printing_universes = b }
let set_printing_wildcard b =
  current_options := { !current_options with printing_wildcard = b }

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
