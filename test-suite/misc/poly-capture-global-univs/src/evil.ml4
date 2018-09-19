
open Stdarg
open EvilImpl

DECLARE PLUGIN "evil_plugin"

VERNAC COMMAND FUNCTIONAL EXTEND VernacEvil CLASSIFIED AS SIDEFF
| [ "Evil" ident(x) ident(y) ] -> [ fun ~atts ~st -> evil x y; st ]
END
