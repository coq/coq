(* record of Printing options *)

type t = {
    allow_match_default_clause : bool;
    coercions : bool;
    compact_contexts : bool;
    existential_instances : bool;
    factorizable_match_patterns : bool;
    implicit: bool;
    implicit_defensive : bool;
    let_binder_types : bool;
    matching : bool;
    notations : bool;
    primitive_projection_compatibility : bool;
    primitive_projection_parameters : bool;
    projections : bool;
    records : bool;
    synth : bool;
    universes : bool;
    wildcard : bool;
  }

let default_options : t = {
    allow_match_default_clause = true;
    coercions = false;
    compact_contexts = false;
    existential_instances = false;
    factorizable_match_patterns = true;
    implicit = false;
    implicit_defensive = true;
    let_binder_types = false;
    matching = true;
    notations = true;
    primitive_projection_compatibility = false;
    primitive_projection_parameters = false;
    projections = false;
    records = true;
    synth = true;
    universes = false;
    wildcard = true;
  }

(* Options for "Printing All" *)
let all_options : t = {
    allow_match_default_clause = false;
    coercions = true;
    compact_contexts = true;
    existential_instances = true;
    factorizable_match_patterns = false;
    implicit = true;
    implicit_defensive = true;
    let_binder_types = true;
    matching = false;
    notations = false;
    primitive_projection_compatibility = true;
    primitive_projection_parameters = true;
    projections = false;
    records = false;
    synth = false;
    universes = true;
    wildcard = false;
  }

(* Negation of "Printing All", that is to say "Sugar All" *)
let sugared_options : t = {
    allow_match_default_clause = not all_options.allow_match_default_clause;
    coercions = not all_options.coercions;
    compact_contexts = not all_options.compact_contexts;
    existential_instances = not all_options.existential_instances;
    factorizable_match_patterns = not all_options.factorizable_match_patterns;
    implicit = not all_options.implicit;
    implicit_defensive = not all_options.implicit_defensive;
    let_binder_types = not all_options.let_binder_types;
    matching = not all_options.matching;
    notations = not all_options.notations;
    primitive_projection_compatibility = not all_options.primitive_projection_compatibility;
    primitive_projection_parameters = not all_options.primitive_projection_parameters;
    projections = not all_options.projections;
    records = not all_options.records;
    synth = not all_options.synth;
    universes = not all_options.universes;
    wildcard = not all_options.wildcard;
  }

let current_options = Summary.ref ~name:"printing options" default_options

let get () = !current_options
let set opts = current_options := opts

(* set printing option, run `f x`, restore options *)
(* can't use Flags.with_option, individual printing options are not references *)
let with_printing_option set_opt f x =
  let saved_opts = get () in
  let _ = set (set_opt saved_opts) in
  try
    let res = f x in
    let _ = set saved_opts in
    res
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    let _ = set saved_opts in
    Exninfo.iraise reraise
