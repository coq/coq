open Pp
open Util
open Names
open Globnames
open Table
open Miniml
open Mlutil
open Common

let json_str s =
  qs s

let json_int i =
  int i

let json_bool b =
  if b then str "true" else str "false"

let json_global typ ref =
  json_str (Common.pp_global typ ref)

let json_id id =
  json_str (Id.to_string id)

let json_dict_one (k, v) =
  json_str k ++ str (": ") ++ v

let json_dict_open l =
  str ("{") ++ fnl () ++
  str ("  ") ++ hov 0 (prlist_with_sep pr_comma json_dict_one l)

let json_dict l =
  json_dict_open l ++ fnl () ++
  str ("}")

let json_list l =
  str ("[") ++ fnl () ++
  str ("  ") ++ hov 0 (prlist_with_sep pr_comma (fun x -> x) l) ++ fnl () ++
  str ("]")

let json_listarr a =
  str ("[") ++ fnl () ++
  str ("  ") ++ hov 0 (prvect_with_sep pr_comma (fun x -> x) a) ++ fnl () ++
  str ("]")


let preamble mod_name comment used_modules usf =
  (match comment with
    | None -> mt ()
    | Some s -> str "/* " ++ hov 0 s ++ str " */" ++ fnl ()) ++
  json_dict_open [
    ("what", json_str "module");
    ("name", json_id mod_name);
    ("need_magic", json_bool (usf.magic));
    ("need_dummy", json_bool (usf.mldummy));
    ("used_modules", json_list
      (List.map (fun mf -> json_str (file_of_modfile mf)) used_modules))
  ]


(*s Pretty-printing of types. *)

let rec json_type vl = function
  | Tmeta _ | Tvar' _ -> assert false
  | Tvar i -> (try
      let varid = List.nth vl (pred i) in json_dict [
        ("what", json_str "type:var");
        ("name", json_id varid)
      ]
    with Failure _ -> json_dict [
        ("what", json_str "type:varidx");
        ("name", json_int i)
      ])
  | Tglob (r, l) -> json_dict [
      ("what", json_str "type:glob");
      ("name", json_global Type r);
      ("args", json_list (List.map (json_type vl) l))
    ]
  | Tarr (t1,t2) -> json_dict [
      ("what", json_str "type:arrow");
      ("left", json_type vl t1);
      ("right", json_type vl t2)
    ]
  | Tdummy _ -> json_dict [("what", json_str "type:dummy")]
  | Tunknown -> json_dict [("what", json_str "type:unknown")]
  | Taxiom -> json_dict [("what", json_str "type:axiom")]


(*s Pretty-printing of expressions. *)

let rec json_expr env = function
  | MLrel n -> json_dict [
      ("what", json_str "expr:rel");
      ("name", json_id (get_db_name n env))
    ]
  | MLapp (f, args) -> json_dict [
      ("what", json_str "expr:apply");
      ("func", json_expr env f);
      ("args", json_list (List.map (json_expr env) args))
    ]
  | MLlam _ as a ->
    let fl, a' = collect_lams a in
    let fl, env' = push_vars (List.map id_of_mlid fl) env in
    json_dict [
      ("what", json_str "expr:lambda");
      ("argnames", json_list (List.map json_id (List.rev fl)));
      ("body", json_expr env' a')
    ]
  | MLletin (id, a1, a2) ->
    let i, env' = push_vars [id_of_mlid id] env in
    json_dict [
      ("what", json_str "expr:let");
      ("name", json_id (List.hd i));
      ("nameval", json_expr env a1);
      ("body", json_expr env' a2)
    ]
  | MLglob r -> json_dict [
      ("what", json_str "expr:global");
      ("name", json_global Term r)
    ]
  | MLcons (_, r, a) -> json_dict [
      ("what", json_str "expr:constructor");
      ("name", json_global Cons r);
      ("args", json_list (List.map (json_expr env) a))
    ]
  | MLtuple l -> json_dict [
      ("what", json_str "expr:tuple");
      ("items", json_list (List.map (json_expr env) l))
    ]
  | MLcase (typ, t, pv) -> json_dict [
      ("what", json_str "expr:case");
      ("expr", json_expr env t);
      ("cases", json_listarr (Array.map (fun x -> json_one_pat env x) pv))
    ]
  | MLfix (i, ids, defs) ->
    let ids', env' = push_vars (List.rev (Array.to_list ids)) env in
    let ids' = Array.of_list (List.rev ids') in
    json_dict [
      ("what", json_str "expr:fix");
      ("funcs", json_listarr (Array.map (fun (fi, ti) ->
        json_dict [
          ("what", json_str "fix:item");
          ("name", json_id fi);
          ("body", json_function env' ti)
        ]) (Array.map2 (fun a b -> a,b) ids' defs)));
      ("for", json_int i);
    ]
  | MLexn s -> json_dict [
      ("what", json_str "expr:exception");
      ("msg", json_str s)
    ]
  | MLdummy _ -> json_dict [("what", json_str "expr:dummy")]
  | MLmagic a -> json_dict [
      ("what", json_str "expr:coerce");
      ("value", json_expr env a)
    ]
  | MLaxiom -> json_dict [("what", json_str "expr:axiom")]
  | MLuint i -> json_dict [
      ("what", json_str "expr:int");
      ("int", json_str (Uint63.to_string i))
    ]

and json_one_pat env (ids,p,t) =
  let ids', env' = push_vars (List.rev_map id_of_mlid ids) env in json_dict [
    ("what", json_str "case");
    ("pat", json_gen_pat (List.rev ids') env' p);
    ("body", json_expr env' t)
  ]

and json_gen_pat ids env = function
  | Pcons (r, l) -> json_cons_pat r (List.map (json_gen_pat ids env) l)
  | Pusual r -> json_cons_pat r (List.map json_id ids)
  | Ptuple l -> json_dict [
      ("what", json_str "pat:tuple");
      ("items", json_list (List.map (json_gen_pat ids env) l))
    ]
  | Pwild -> json_dict [("what", json_str "pat:wild")]
  | Prel n -> json_dict [
      ("what", json_str "pat:rel");
      ("name", json_id (get_db_name n env))
    ]

and json_cons_pat r ppl = json_dict [
    ("what", json_str "pat:constructor");
    ("name", json_global Cons r);
    ("argnames", json_list ppl)
  ]

and json_function env t =
  let bl, t' = collect_lams t in
  let bl, env' = push_vars (List.map id_of_mlid bl) env in
  json_dict [
    ("what", json_str "expr:lambda");
    ("argnames", json_list (List.map json_id (List.rev bl)));
    ("body", json_expr env' t')
  ]


(*s Pretty-printing of inductive types declaration. *)

let json_ind ip pl cv = json_dict [
    ("what", json_str "decl:ind");
    ("name", json_global Type (IndRef ip));
    ("argnames", json_list (List.map json_id pl));
    ("constructors", json_listarr (Array.mapi (fun idx c -> json_dict [
        ("name", json_global Cons (ConstructRef (ip, idx+1)));
        ("argtypes", json_list (List.map (json_type pl) c))
      ]) cv))
  ]


(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind (kn, defs) -> prvecti_with_sep pr_comma
    (fun i p -> if p.ip_logical then str ""
     else json_ind (kn, i) p.ip_vars p.ip_types) defs.ind_packets
  | Dtype (r, l, t) -> json_dict [
      ("what", json_str "decl:type");
      ("name", json_global Type r);
      ("argnames", json_list (List.map json_id l));
      ("value", json_type l t)
    ]
  | Dfix (rv, defs, typs) -> json_dict [
      ("what", json_str "decl:fixgroup");
      ("fixlist", json_listarr (Array.mapi (fun i r ->
        json_dict [
          ("what", json_str "fixgroup:item");
          ("name", json_global Term rv.(i));
          ("type", json_type [] typs.(i));
          ("value", json_function (empty_env ()) defs.(i))
        ]) rv))
    ]
  | Dterm (r, a, t) -> json_dict [
      ("what", json_str "decl:term");
      ("name", json_global Term r);
      ("type", json_type [] t);
      ("value", json_function (empty_env ()) a)
    ]

let rec pp_structure_elem = function
  | (l,SEdecl d) -> [ pp_decl d ]
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr
  | (l,SEmodtype m) -> []
      (* for the moment we simply discard module type *)

and pp_module_expr = function
  | MEstruct (mp,sel) -> List.concat (List.map pp_structure_elem sel)
  | MEfunctor _ -> []
      (* for the moment we simply discard unapplied functors *)
  | MEident _ | MEapply _ -> assert false
      (* should be expansed in extract_env *)

let pp_struct mls =
  let pp_sel (mp,sel) =
    push_visible mp [];
    let p = prlist_with_sep pr_comma identity
      (List.concat (List.map pp_structure_elem sel)) in
    pop_visible (); p
  in
  str "," ++ fnl () ++
  str "  " ++ qs "declarations" ++ str ": [" ++ fnl () ++
  str "    " ++ hov 0 (prlist_with_sep pr_comma pp_sel mls) ++ fnl () ++
  str "  ]" ++ fnl () ++
  str "}" ++ fnl ()


let json_descr = {
  keywords = Id.Set.empty;
  file_suffix = ".json";
  file_naming = file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
