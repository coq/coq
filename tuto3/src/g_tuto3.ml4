DECLARE PLUGIN "tuto3_plugin"

open Ltac_plugin
open Pp
(* This one is necessary, to avoid message about missing wit_string *)
open Stdarg

VERNAC COMMAND EXTEND ShowOneConstruction CLASSIFIED AS QUERY
| [ "Tuto3_1" ] ->
  [ let gr_S =
        Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
    (* the long name of "S" was found with the command "About S." *)
    let gr_O =
        Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
    let c_S = EConstr.of_constr (Universes.constr_of_global gr_S) in
    let c_O = EConstr.of_constr (Universes.constr_of_global gr_O) in
    let c_v = EConstr.mkApp (c_S, [| c_O |]) in
    let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, s = Evd.new_sort_variable Evd.univ_rigid evd in
    let new_type_2 = Constr.mkSort s in
    let evd, bare_evar = Evd.new_evar evd
        (Evd.make_evar (Environ.named_context_val env) new_type_2) in
    let arg_type = EConstr.mkEvar (bare_evar, [| |]) in
    let c_f =
       EConstr.mkLambda(Names.Name (Names.Id.of_string "x"), arg_type,
          EConstr.mkRel 1) in
    let c_1 = EConstr.mkApp (c_f, [| c_v |]) in
    (* type verification happens here.  In this case, we don't care about
       the type, but usually, typing will update existential variables and
       universes, all this being stored in the new "evar_map" object *)
    let evd, _ =
      Typing.type_of (Global.env()) (Evd.from_env (Global.env())) c_1 in
    ()
(*    Feedback.msg_notice
      (Termops.print_constr_env (Global.env()) evd c_1) *) ]
END
