let to_string = function
  | `X11 -> "X11"
  | `QUARTZ -> "QUARTZ"
  | `WIN32 -> "WIN32"

let main () = Format.printf "%s%!" (to_string Coq_config.gtk_platform)

let () = main ()
