
(** Some architectures may have a native ocaml compiler but no native
    dynlink.cmxa (e.g. ARM). If you still want to build a native coqtop
    there, you'll need this dummy implementation of Dynlink.
    Compile it and install with:

      ocamlopt -a -o dynlink.cmxa dynlink.ml
      sudo cp -i dynlink.cmxa `ocamlopt -where`

    Then build coq this way: ./configure -natdynlink no && make world
*)

let is_native = true (* This file will only be given to the native compiler *)

type linking_error =
| Undefined_global of string
| Unavailable_primitive of string
| Uninitialized_global of string

type error =
| Not_a_bytecode_file of string
| Inconsistent_import of string
| Unavailable_unit of string
| Unsafe_file
| Linking_error of string * linking_error
| Corrupted_interface of string
| File_not_found of string
| Cannot_open_dll of string
| Inconsistent_implementation of string

exception Error of error

let error_message = function
  | Not_a_bytecode_file s -> "Native dynamic link not supported (module "^s^")"
  | _ -> "Native dynamic link not supported"

let loadfile : string -> unit = fun s -> raise (Error (Not_a_bytecode_file s))
let loadfile_private = loadfile

let adapt_filename s = s

let init () = ()
let allow_only : string list -> unit = fun _ -> ()
let prohibit : string list -> unit = fun _ -> ()
let default_available_units : unit -> unit = fun _ -> ()
let allow_unsafe_modules : bool -> unit = fun _ -> ()
let add_interfaces : string list -> string list -> unit = fun _ _ -> ()
let add_available_units : (string * Digest.t) list -> unit = fun _ -> ()
let clear_available_units : unit -> unit = fun _ -> ()
let digest_interface : string -> string list -> Digest.t =
 fun _ _ -> failwith "digest_interface"
