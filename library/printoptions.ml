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

(* use negation of corresponding fields in all_options *)
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

let saved_options = Summary.ref ~name:"saved printing options" None

let get_saved_options () = !saved_options
let set_saved_options opts = saved_options := opts

(* given a print options record, get list of option names and their values,
   used when setting options locally
   somewhat redundant with the option declarations, so a bit fragile
 *)
let options_by_name_value opts =
  [ (["Printing";"Allow";"Match";"Default";"Clause"],opts.allow_match_default_clause);
    (["Printing";"Coercions"],opts.coercions);
    (["Printing";"Compact";"Contexts"],opts.compact_contexts);
    (["Printing";"Existential";"Instances"],opts.existential_instances);
    (["Printing";"Factorizable";"Match";"Patterns"],opts.factorizable_match_patterns);
    (["Printing";"Implicit"],opts.implicit);
    (["Printing";"Implicit";"Defensive"],opts.implicit_defensive);
    (["Printing";"Let";"Binder";"Types"],opts.let_binder_types);
    (["Printing";"Matching"],opts.matching);
    (["Printing";"Notations"],opts.notations);
    (["Printing";"Primitive";"Projection";"Compatibility"],opts.primitive_projection_compatibility);
    (["Printing";"Primitive";"Projection";"Parameters"],opts.primitive_projection_parameters);
    (["Printing";"Projections"],opts.projections);
    (["Printing";"Records"],opts.records);
    (["Printing";"Synth"],opts.synth);
    (["Printing";"Universes"],opts.universes);
    (["Printing";"Wildcard"],opts.wildcard);
  ]

let all_names_values     = options_by_name_value all_options
let sugared_names_values = options_by_name_value sugared_options
let default_names_values = options_by_name_value default_options

let mk_printing_local opts_vals =
  List.iter
    (fun (opt,b) ->
      Goptions.(set_bool_option_value_gen ~locality:OptLocal opt b))
    opts_vals

let set_printing_all_global () = set all_options
let set_printing_all_local () = mk_printing_local all_names_values

let set_printing_all ~local =
  set_saved_options (Some (get ()));
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
     set opts;
     set_saved_options None
  | None -> noop_unset_printing_all_warning ()

let set_printing_sugared_global () = set sugared_options
let set_printing_sugared_local () = mk_printing_local sugared_names_values

let set_printing_sugared ~local =
  if local then
    set_printing_sugared_local ()
  else
    set_printing_sugared_global ()

let set_printing_defaults_global () = set default_options
let set_printing_defaults_local () = mk_printing_local default_names_values

let set_printing_defaults ~local =
  if local then
    set_printing_defaults_local ()
  else
    set_printing_defaults_global ()

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
