open Utest
open Names
open Constr
open Declarations

let log_out_ch = open_log_out_ch __FILE__

let linking_test = mk_test "vm-block-deferred-linking" (OUnit.TestCase (fun () ->
  let env = Environ.empty_env in
  let kn = Constant.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string "VmBlockTest"]))
      (Id.of_string "body_only")) in
  (* A deliberately uncompiled but otherwise ordinary constant. Its slot
     raises vm-uncompiled-constant if any linker attempts to resolve it. *)
  let cb = {
    const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = Def mkProp;
    const_type = mkSet;
    const_relevance = Sorts.Relevant;
    const_body_code = Vmemitcodes.BCuncompiled;
    const_universes = Monomorphic;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  } in
  let env = Environ.add_constant kn cb env in
  let _, key = Environ.lookup_constant_key kn env in
  let sigma = Genlambda.empty_evars env in
  let inner = mkPBlock (UVars.Instance.empty, mkSet, [||], mkConstU (kn, UVars.Instance.empty)) in
  let outer = mkPBlock (UVars.Instance.empty, mkSet, [||], inner) in
  let outer = Vmsymtable.val_of_constr env sigma outer in
  OUnit.assert_bool "parent must not link body-only constant" (!key = None);
  let block v = match Vmvalues.whd_val v with
    | Values.Vaccu (Vmvalues.Ablock b, []) -> b
    | _ -> OUnit.assert_failure "expected suspended block"
  in
  let inner = (block outer).Vmvalues.blocked_force () in
  OUnit.assert_bool "forcing outer must not link nested body" (!key = None);
  let b = block inner in
  let rejected = try ignore (b.Vmvalues.blocked_force ()); false with
    | exn when CErrors.noncritical exn -> true
  in
  OUnit.assert_bool "forcing inner must attempt body linking" rejected;
  OUnit.assert_bool "source survives a failed force"
    (Constr.equal b.Vmvalues.blocked_source.Vmvalues.block_term
      (mkPBlock (UVars.Instance.empty, mkSet, [||], mkConstU (kn, UVars.Instance.empty))));
))

let reentry_test = mk_test "vm-block-reentrant-global-growth" (OUnit.TestCase (fun () ->
  let env = ref Environ.empty_env in
  let path = ModPath.MPfile (DirPath.make [Id.of_string "VmBlockGrowth"]) in
  let add name ty =
    let kn = Constant.make1 (KerName.make path (Id.of_string name)) in
    let cb = {
      const_hyps = [];
      const_univ_hyps = UVars.Instance.empty;
      const_body = Undef None;
      const_type = ty;
      const_relevance = Sorts.Relevant;
      const_body_code = Vmemitcodes.BCconstant;
      const_universes = Monomorphic;
      const_inline_code = false;
      const_typing_flags = Environ.typing_flags !env;
    } in
    env := Environ.add_constant kn cb !env;
    mkConstU (kn, UVars.Instance.empty)
  in
  (* More than the initial global-table capacity; these globals are referenced
     only by a deferred function body. Forcing also exercises stack growth. *)
  let n = 4100 in
  let args = Array.init n (fun i -> add ("arg" ^ string_of_int i) mkSet) in
  let fty = ref mkSet in
  for _ = 1 to n do fty := mkProd (Context.anonR, mkSet, !fty) done;
  let f = add "f" !fty in
  let ty = mkProd (Context.anonR, mkSet, mkSet) in
  let payload = mkLambda (Context.anonR, mkSet, mkApp (f, args)) in
  let b = mkPBlock (UVars.Instance.empty, ty, [||], payload) in
  let identity = mkLambda (Context.anonR, ty, mkRel 1) in
  (* The newly linked closure executes in the outer interpreter AFTER RUN's
     callback returns, so that interpreter must refresh its global array. *)
  let term = mkApp (mkPRun (ty, ty, b, identity), [|mkProp|]) in
  let value = Vmsymtable.val_of_constr !env (Genlambda.empty_evars !env) term in
  match Vmvalues.whd_val value with
  | Values.Vaccu (_, [Vmvalues.Zapp args]) ->
    OUnit.assert_equal ~msg:"all deferred arguments survive re-entry" n (Vmvalues.nargs args)
  | _ -> OUnit.assert_failure "expected applied neutral after re-entry"
))

let () = run_tests __FILE__ log_out_ch [linking_test; reentry_test]
