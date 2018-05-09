DECLARE PLUGIN "tuto3_plugin"

open Ltac_plugin
open Pp
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
| [ "Tuto3_2" ] ->
  [ let gr_S =
        Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
    (* the long name of "S" was found with the command "About S." *)
    let gr_O =
        Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
    let c_O = EConstr.of_constr (Universes.constr_of_global gr_O) in
    let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, s = Evd.new_sort_variable Evd.univ_rigid evd in
    let new_type_2 = EConstr.mkSort s in
    let evd, arg_type = Evarutil.new_evar env evd new_type_2 in
    let c_f =
       EConstr.mkLambda(Names.Name (Names.Id.of_string "x"), arg_type,
          EConstr.mkRel 1) in
    let c_1 = EConstr.mkApp (c_f, [| c_O |]) in
    (* type verification happens here.  Type verification will update
       existential variable information in the evd part. *)
    let evd, the_type =
      Typing.type_of (Global.env()) evd c_1 in
    Feedback.msg_notice
      ((Termops.print_constr_env env evd c_1) ++
       str " has type " ++
       (Termops.print_constr_env env evd the_type)) ]
END
