(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

module F = Format

type 'a pp = Format.formatter -> 'a -> unit

module Rule = struct
  type t =
    { targets : string list
    ; deps : string list
    ; action : string
    ; alias : string option
    }

  let pp_sep fmt () = F.fprintf fmt "@;"
  let ppl = F.pp_print_list ~pp_sep F.pp_print_string
  let pp_alias fmt = function
    | None -> ()
    | Some alias -> F.fprintf fmt "(alias %s)@\n" alias

  let pp fmt { alias; targets; deps; action } =
    F.fprintf fmt
      "@[(rule@\n @[%a(targets @[%a@])@\n(deps @[%a@])@\n(action @[%a@])@])@]@\n"
      pp_alias alias ppl targets ppl deps F.pp_print_string action
end

module Install = struct
  type t =
    { section : string
    ; package : string
    ; files : (string * string) list
    (* (source as target) *)
    }

  let pp_install_file fmt (source, target) =
    F.fprintf fmt "(%s as %s)" source target

  let pp fmt { section; package; files } =
    F.fprintf fmt
      "@[(install@\n @[(section @[%s@])@\n(package @[%s@])@\n(files @[%a@])@])@]@\n"
      section package (F.pp_print_list pp_install_file) files

end

module Subdir = struct

  type 'a t = { subdir : string; payload : 'a }

  let pp ppf fmt { subdir; payload } =
    if String.equal subdir "" then
      ppf fmt payload
    else
      Fun.protect ~finally:(fun () -> F.fprintf fmt "@])@\n")
        (fun () ->
           F.fprintf fmt "(subdir %s@\n @[" subdir;
           ppf fmt payload)

end
