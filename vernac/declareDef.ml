type locality = Declare.locality =
  | Discharge [@ocaml.deprecated "Use [Declare.Discharge]"]
  | Global of Declare.import_status [@ocaml.deprecated "Use [Declare.Global]"]
[@@ocaml.deprecated "Use [Declare.locality]"]

let declare_definition = Declare.declare_definition
[@@ocaml.deprecated "Use [Declare.declare_definition]"]
module Hook = Declare.Hook
[@@ocaml.deprecated "Use [Declare.Hook]"]
