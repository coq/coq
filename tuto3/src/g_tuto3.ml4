DECLARE PLUGIN "tuto3_plugin"

open Ltac_plugin
open Pp

open Construction_game

(* This one is necessary, to avoid message about missing wit_string *)
open Stdarg

VERNAC COMMAND EXTEND ShowTypeConstruction CLASSIFIED AS QUERY
| [ "Tuto3_1" ] ->
  [ let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, s = Evd.new_sort_variable Evd.univ_rigid evd in
    let new_type_2 = EConstr.mkSort s in
    let evd, _ =
      Typing.type_of (Global.env()) (Evd.from_env (Global.env())) new_type_2 in
    Feedback.msg_notice
      (Termops.print_constr_env env evd new_type_2) ]
END

VERNAC COMMAND EXTEND ShowOneConstruction CLASSIFIED AS QUERY
| [ "Tuto3_2" ] -> [ example_sort_app_lambda() ]
END

