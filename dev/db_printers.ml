open Pp
open Names

let pP s = pP (hOV 0 s)

let prid id = Format.print_string (string_of_id id)
let prsp sp = Format.print_string (string_of_path sp)


