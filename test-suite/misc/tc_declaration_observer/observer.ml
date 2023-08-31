
let o = open_out "main.out"

let observe x =
  let open Classes in
  let open Event in
  let open Typeclasses in
  let open Hints in
  let p = Pp.string_of_ppcmds in
  match x with
  | NewClass { cl_impl } ->
      Printf.fprintf o "NewClass %s\n" (p (Printer.pr_global cl_impl))
  | NewInstance { instance ; info = { hint_priority }; locality } ->
      Printf.fprintf o "NewInstance %s %s %s\n"
        (p (Printer.pr_global instance))
        (p (Pp.pr_opt Pp.int hint_priority))
        (if locality = Local then "local" else "")

let obs = Classes.register_observer ~name:"test observer" observe

let () = Classes.activate_observer obs
