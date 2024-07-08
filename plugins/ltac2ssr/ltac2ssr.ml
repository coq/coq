open Names
open Ltac2_plugin
open Ssreflect_plugin
open Tac2expr


let add_scope s f =
  Tac2entries.register_scope (Id.of_string s) f

let rec pr_scope = let open CAst in let open Pp in function
| SexprStr {v=s} -> qstring s
| SexprInt {v=n} -> Pp.int n
| SexprRec (_, {v=na}, args) ->
  let na = match na with
  | None -> str "_"
  | Some id -> Id.print id
  in
  na ++ str "(" ++ prlist_with_sep (fun () -> str ", ") pr_scope args ++ str ")"

let scope_fail s args =
  let open Pp in
  let args = str "(" ++ prlist_with_sep (fun () -> str ", ") pr_scope args ++ str ")" in
  CErrors.user_err (str "Invalid arguments " ++ args ++ str " in scope " ++ str s)

let add_expr_scope name entry f =
  add_scope name begin function
  | [] -> Tac2entries.ScopeRule (Pcoq.Symbol.nterm entry, f)
  | arg -> scope_fail name arg
  end


let ipat_tag = Tac2dyn.Val.create "ssr.ipat"
let ipat = Tac2ffi.repr_ext ipat_tag
let gtypref kn = GTypRef (Other kn, [])

let ssr_prefix n = KerName.make (ModPath.MPfile (DirPath.make (List.rev_map Id.of_string ["Ltac2ssr";"Ipat"]))) (Label.of_id (Id.of_string_soft n))

let wit_ipat : (Ssrast.ssripat, Ssrast.ssripat) Tac2dyn.Arg.tag =
  Tac2dyn.Arg.create "ipat"

  (* TODO: add loc *)
let () =
  let open Pp in
  let open Tac2env in
  let t_ipat = ssr_prefix "ipat" in 
  let interp _ ip = Proofview.tclUNIT (Tac2ffi.of_ext ipat_tag ip) in
  let print _ _ ip = str "ipat:(" ++ str "TODO" ++ str ")" in
  let obj = {
    ml_intern = (fun _ _ id -> GlbVal id, gtypref t_ipat);
    ml_interp = interp;
    ml_subst = (fun _ id -> id);
    ml_print = print;
    ml_raw_print = print;
  } in
  define_ml_object wit_ipat obj

let of_ipat x = CAst.make @@ CTacExt (wit_ipat,x)

let of_ssripats =
  Tac2quote.of_list of_ipat

let () = add_expr_scope "ipats" Ssrparser.Ltac2.ssripats of_ssripats

let pname s = { mltac_plugin = "coq-core.plugins.ltac2ssr"; mltac_tactic = s }

let () =
  let open Tac2externals in
  let open Tac2ffi in
  define (pname "move_up") (list ipat @-> tac unit) (fun x -> Ssripats.(tclIPAT (tclCompileIPats x)))
