(* Main coqtop initialization *)
let () =
  (* XXX: We should make this a configure option *)
  List.iter Mltop.add_known_module Str.(split (regexp " ") Tolink.static_modules);
  (* Start the toplevel loop *)
  Coqtop.start()
