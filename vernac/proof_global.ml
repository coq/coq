(* compatibility module; can be removed once we agree on the API *)

type t = Declare.Proof.t
[@@ocaml.deprecated "Use [Declare.Proof.t]"]
let map_proof = Declare.Proof.map_proof
[@@ocaml.deprecated "Use [Declare.Proof.map_proof]"]
let get_proof = Declare.Proof.get_proof
[@@ocaml.deprecated "Use [Declare.Proof.get_proof]"]

type opacity_flag = Declare.opacity_flag =
  | Opaque [@ocaml.deprecated "Use [Declare.Opaque]"]
  | Transparent [@ocaml.deprecated "Use [Declare.Transparent]"]
[@@ocaml.deprecated "Use [Declare.opacity_flag]"]
