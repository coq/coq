open Arg

let quoted = ref false
let trailing_slash = ref false

let arguments = [
  "-quoted",Set quoted, "Quote path";
  "-trailing-slash",Set trailing_slash, "End the path with a /";
]
let subject = ref None
let set_subject x =
  if !subject <> None then
    failwith "only one path";
  subject := Some x

let () =
  Arg.parse arguments set_subject "Usage:";
  let subject =
    match !subject with
    | None -> failwith "no path given";
    | Some x -> x in
  Sys.chdir subject;
  let dir = Sys.getcwd () in
  let dir = if !trailing_slash then dir ^ "/" else dir in
  let dir = if !quoted then Filename.quote dir else dir in
  Format.printf "%s%!" dir
