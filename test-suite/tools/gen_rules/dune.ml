(* Some helper functions form formatting lists and strings *)
let rec pp_list sep pp fmt = function
  | []  -> ()
  | [l] -> Format.fprintf fmt "%a" pp l
  | x::xs -> Format.fprintf fmt "%a%a%a" pp x sep () (pp_list sep pp) xs

let sep fmt () = Format.fprintf fmt "@;"

let ppl = pp_list sep Format.pp_print_string

(* Dune rule formatting API *)
(* TODO: make into proper API *)

(** Action formatting API *)
module Action = struct
  module Outputs = struct
    type t = Stdout | Stderr | Outputs
    let pp fmt = function
    | Stdout -> Format.fprintf fmt "stdout"
    | Stderr -> Format.fprintf fmt "stderr"
    | Outputs -> Format.fprintf fmt "outputs"
  end

  (** Various actions a dune rule can have. This list is of course incomplete.
    *)
  type t =
  | Setenv of (string * string) * t
  | With_outputs_to of Outputs.t * string * t
  | With_accepted_exit_codes of string * t
  | With_stdin_from of string * t
  | Progn of t list
  | Pipe_outputs of t list
  | Diff of string * string
  | Run of string list
  | No_infer of t
  | Copy of string * string

  let pp fmt action =
    let rec pp_action fmt = function
    | Setenv ((envvar, envval), dsl) -> Format.fprintf fmt "@[(setenv %s %s@ %a)@]" envvar envval pp_action dsl
    | With_outputs_to (outputs, file, dsl) -> Format.fprintf fmt "@[<1>(with-%a-to %s@ %a)@]" Outputs.pp outputs file pp_action dsl
    | With_accepted_exit_codes (codes, dsl) -> Format.fprintf fmt "@[<1>(with-accepted-exit-codes %s@ %a)@]" codes pp_action dsl
    | With_stdin_from (in_file, dsl) -> Format.fprintf fmt "@[<1>(with-stdin-from %s@ %a)@]" in_file pp_action dsl
    | Diff (file1, file2) -> Format.fprintf fmt "@[<1>(diff@ %s@ %s)@]" file1 file2
    | Progn dsls -> Format.fprintf fmt "@[<1>(progn@ %a)@]" (pp_list sep pp_action) dsls
    | Pipe_outputs dsls -> Format.fprintf fmt "@[<1>(pipe-outputs@ %a)@]" (pp_list sep pp_action) dsls
    | Run run -> Format.fprintf fmt "@[<1>(run %a)@]" (pp_list sep Format.pp_print_string) run
    | No_infer dsl -> Format.fprintf fmt "@[<1>(no-infer %a)@]" pp_action dsl
    | Copy (file1, file2) -> Format.fprintf fmt "@[<1>(copy@ %s@ %s)@]" file1 file2
    in
    Format.fprintf fmt "@[<v1>(action@ %a)@]" pp_action action

  (* Smart constructors *)
  let rec setenv_batch envs action = match envs with
  | envpair :: envs -> Setenv (envpair, setenv_batch envs action)
  | [] -> action

  let with_stdin_from_opt in_file action = match in_file with
    | Some in_file -> With_stdin_from (in_file, action)
    | None -> action

  let with_accepted_exit_codes_list exit_codes dsl =
    let exit_codes_to_string = function
      | [] -> "0"
      | l -> Printf.sprintf "(or %s)" @@ String.concat " " (List.map string_of_int l)
    in
    match exit_codes with
    | [] -> dsl
    | exit_codes -> With_accepted_exit_codes (exit_codes_to_string exit_codes, dsl)

  let with_outputs_to_opt outputs log_file dsl = match log_file with
    | Some log_file -> With_outputs_to (outputs, log_file, dsl)
    | None -> dsl

end

(** Rule formatting API *)
module Rule = struct
  type t =
    { targets : string list
    ; deps : string list
    ; action : Action.t
    ; alias : string option
    }

  let pp_alias fmt = function
    | None -> ()
    | Some alias -> Format.fprintf fmt "@[(alias @[%s@])@]@ " alias

  let pp_targets fmt = function
    | [] -> ()
    | ts -> Format.fprintf fmt "@[(targets @[<v>%a@])@]@ " ppl ts

  let pp_deps fmt = function
    | [] -> ()
    | ds -> Format.fprintf fmt "@[(deps @[<v>%a@])@]@ " ppl ds

  let pp_action fmt action =
    Format.fprintf fmt "@[(action @[<v>%a@])@]@ " Format.pp_print_string action

  let pp fmt { alias; targets; deps; action } =
    Format.fprintf fmt
      "@[<1>(rule@,@[<v>%a%a%a%a@])@]@,"
      pp_alias alias
      pp_targets targets
      pp_deps deps
      Action.pp action
end

(** Collection of predefined dune rules. *)
module Rules = struct
  (** Diffing two files. *)
  let diff ~out ?(alias=Some "runtest") file1 file2 =
    let rule_diff =
      Rule.{ targets = []
      ; deps = [file1; file2]
      ; action = Action.Diff (file1, file2)
      ; alias
      } in
      Rule.pp out rule_diff

  (** Run rule, [~run] is a list of string consisting of a command and its arguments. *)
  let run ~run ~out ?log_file ?(log_outputs=Action.Outputs.Outputs) ?in_file ?(alias=Some "runtest") ?(envs=[]) ?(exit_codes=[]) ?(targets=[]) ?(deps=[]) () =
    let action =
      Action.Run run
      |> Action.with_stdin_from_opt in_file
      |> Action.with_accepted_exit_codes_list exit_codes
      |> Action.with_outputs_to_opt log_outputs log_file
      |> Action.setenv_batch envs
    in
    Rule.pp out Rule.{ targets; deps; action; alias }

  (** Format inside a subdir stanza *)
  let in_subdir fmt dir ~f =
    Format.fprintf fmt "@[<1>(subdir %s@,@[<v>%a@])@]@," dir f ()

  (** Variant of run that takes a list of runs and pipes them *)
  let run_pipe ~runs ~out ?log_file ?(log_outputs=Action.Outputs.Outputs) ?in_file ?(alias=Some "runtest") ?(envs=[]) ?(exit_codes=[]) ?(targets=[]) ?(deps=[]) () =
    let action =
      runs
      |> List.map (fun x -> Action.Run x)
      |> fun x -> Action.Pipe_outputs x
      |> Action.with_stdin_from_opt in_file
      |> Action.with_accepted_exit_codes_list exit_codes
      |> Action.with_outputs_to_opt log_outputs log_file
      |> Action.setenv_batch envs
    in
    Rule.pp out Rule.{ targets; deps; action; alias }

  let copy ~out ?alias src dst =
    Rule.pp out Rule.{
      targets = [dst]
      ; deps = [src]
      ; action = Action.Copy (src, dst)
      ; alias
      }

end

module Env = struct
  module Profile = struct
    type t = string option

    let pp fmt = function
      | None -> Format.fprintf fmt "_"
      | Some profile -> Format.fprintf fmt "%s" profile
  end

  module Setting = struct
    type t =
    | Binaries of string list

    let pp fmt = function
      | Binaries binaries -> Format.fprintf fmt "@[<1>(binaries@ %a)@]" ppl binaries
  end

  module Settings = struct
    type t = Setting.t list

    let pp fmt settings =
      Format.fprintf fmt "@[<v>%a@]" (pp_list sep Setting.pp) settings
  end

  type t = (Profile.t * Settings.t) list

  let pp fmt =
    Format.fprintf fmt "@[<1>(env@ %a)@]@," (pp_list sep (fun fmt x ->
      Format.fprintf fmt "@[<1>(%a@ %a)@]" Profile.pp (fst x) Settings.pp (snd x)))
end

module Alias = struct
  type t = {
    name : string;
    deps : string list;
  }

  let pp fmt { name; deps } =
    Format.fprintf fmt "@[<1>(alias@ (name %s)@ (deps %a))@]@," name ppl deps
end
