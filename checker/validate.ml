
let rec pr_obj o =
  if Obj.is_int o then
    Format.print_string ("INT:"^string_of_int(Obj.magic o))
  else if Obj.is_block o then
    let t = Obj.tag o in
    if t > Obj.no_scan_tag then
      if t = Obj.string_tag then
        Format.print_string ("STR:"^Obj.magic o)
      else
        Format.print_string "?"
    else
      (let n = Obj.size o in
      Format.print_string ("#"^string_of_int t^"(");
      Format.open_hvbox 0;
      for i = 0 to n-1 do
        pr_obj (Obj.field o i);
        if i<>n-1 then (Format.print_string ","; Format.print_cut())
      done;
      Format.close_box();
      Format.print_string ")")
  else Format.print_string "?"

let pr_obj o = pr_obj o; Format.print_newline()



let no_val (o:Obj.t) = ()

let val_tag t o =
  if Obj.is_block o && Obj.tag o = t then ()
  else failwith ("tag "^string_of_int t)

let val_tuple s v o =
  let n = Array.length v in
  if Obj.is_block o then
    if Obj.size o = n then
      Array.iteri (fun i f -> f (Obj.field o i)) v
    else
      (pr_obj o;
       failwith
         ("tuple:" ^s^" size found:"^string_of_int (Obj.size o)))
  else failwith ("tuple:" ^s)

let val_sum s cc vv o =
  if Obj.is_block o then
    let n = Array.length vv in
    let i = Obj.tag o in
    if i < n then val_tuple (s^"("^string_of_int i^")") vv.(i) o
    else failwith ("bad tag in sum: "^string_of_int i)
  else if Obj.is_int o then
    let (n:int) = Obj.magic o in
    (if n<0 || n>=cc then failwith "bad constant constructor")
  else failwith "not a sum"

let val_array f o =
  if Obj.is_block o then
    for i = 0 to Obj.size o - 1 do
      (f (Obj.field o i):unit)
    done
  else failwith "not array"
(*
let val_tuple s v o =
  prerr_endline ("TUPLE "^s);
  val_tuple s v o;
  prerr_endline ("END "^s)
let val_sum s cc vv o =
  prerr_endline ("SUM "^s);
  val_sum s cc vv o;
  prerr_endline ("END "^s)
let val_array f o =
  prerr_endline "ARRAY";
  val_array f o;
  prerr_endline "END ARRAY"
*)
let val_int o = if not (Obj.is_int o) then failwith "not int"
(*; prerr_endline "INT"
*)
let val_str s = val_tag Obj.string_tag s
(*; prerr_endline ("STR "^Obj.magic s)*)

let val_bool o = val_sum "bool" 2 [||] o

let val_opt f = val_sum "option" 1 [|[|f|]|]

let rec val_list f o =
  val_sum "list" 1 [|[|f;val_list f|]|] o

let val_ref f = val_tuple "ref" [|f|]

let rec val_set f o =
  val_sum "set" 1 [|[|val_set f;f;val_set f;val_int|]|] o
let rec val_map fk fv o =
  val_sum "map" 1 [|[|val_map fk fv;fk;fv;val_map fk fv;val_int|]|] o

(* Coq *)

let val_id = val_str

let val_dp = val_list val_id

let val_name = val_sum "name" 1 [|[|val_id|]|]

let val_uid = val_tuple "uid" [|val_int;val_str;val_dp|]

let rec val_mp o =
  val_sum "mp" 0 [|[|val_dp|];[|val_uid|];[|val_uid|];[|val_mp;val_id|]|] o

let val_kn = val_tuple "kn" [|val_mp;val_dp;val_id|]

let val_ind = val_tuple "ind"[|val_kn;val_int|]
let val_cstr = val_tuple "cstr"[|val_ind;val_int|]

let val_ci = no_val

let val_cast = no_val

let val_level = val_sum "level" 1 [|[|val_dp;val_int|]|]
let val_univ = val_sum "univ" 0
  [|[|val_level|];[|val_list val_level;val_list val_level|]|]

let val_cstrs =
  val_set (val_tuple"univ_cstr"[|val_level;val_sum "order" 3[||];val_level|])

let val_sort = val_sum "sort" 0 [|[|val_sum "cnt" 2 [||]|];[|val_univ|]|]
let val_sortfam = val_sum "sort_family" 3 [||]

let val_evar f = val_tuple "evar" [|val_int;val_array f|]

let val_prec f =
  val_tuple "prec"[|val_array val_name; val_array f; val_array f|]
let val_fix f =
  val_tuple"fix1"[|val_tuple"fix2"[|val_array val_int;val_int|];val_prec f|]
let val_cofix f = val_tuple"cofix"[|val_int;val_prec f|]


let rec val_constr o = val_sum "constr" 0 [|
  [|val_int|]; (* Rel *)
  [|val_id|]; (* Var *)
  [|val_int|]; (* Meta *)
  [|val_evar val_constr|]; (* Evar *)
  [|val_sort|]; (* Sort *)
  [|val_constr;val_cast;val_constr|]; (* Cast *)
  [|val_name;val_constr;val_constr|]; (* Prod *)
  [|val_name;val_constr;val_constr|]; (* Lambda *)
  [|val_name;val_constr;val_constr;val_constr|]; (* LetIn *)
  [|val_constr;val_array val_constr|]; (* App *)
  [|val_kn|]; (* Const *)
  [|val_ind|]; (* Ind *)
  [|val_cstr|]; (* Construct *)
  [|val_ci;val_constr;val_constr;val_array val_constr|]; (* Case *)
  [|val_fix val_constr|]; (* Fix *)
  [|val_cofix val_constr|] (* CoFix *)
|] o


let val_ndecl = val_tuple"ndecl"[|val_id;val_opt val_constr;val_constr|]
let val_rdecl = val_tuple"rdecl"[|val_name;val_opt val_constr;val_constr|]
let val_nctxt = val_list val_ndecl
let val_rctxt = val_list val_rdecl

let val_arity = val_tuple"arity"[|val_rctxt;val_constr|]

let val_eng = val_sum "eng" 1 [||]

let val_pol_arity = val_tuple"pol_arity"[|val_list(val_opt val_univ);val_univ|]
let val_cst_type =
  val_sum "cst_type" 0 [|[|val_constr|];[|val_rctxt;val_pol_arity|]|]

let val_subst_dom =
  val_sum "subst_dom" 0 [|[|val_uid|];[|val_uid|];[|val_mp|]|]


let val_res = val_opt no_val

let val_subst =
  val_map val_subst_dom (val_tuple "subst range" [|val_mp;val_res|])

let val_cstr_subst =
  val_ref (val_sum "cstr_subst" 0 [|[|val_constr|];[|val_subst;val_constr|]|])

let val_cb = val_tuple "cb"
  [|val_nctxt;val_opt val_cstr_subst; val_cst_type;no_val;val_cstrs;
    val_bool; val_bool |]

let val_recarg = val_sum "recarg" 1 [|[|val_int|];[|val_ind|]|]

let rec val_wfp o = val_sum "wf_paths" 0
  [|[|val_int;val_int|];[|val_recarg;val_array val_wfp|];
    [|val_int;val_array val_wfp|]|] o

let val_mono_ind_arity = val_tuple"mono_ind_arity"[|val_constr;val_sort|]
let val_ind_arity = val_sum "ind_arity" 0
  [|[|val_mono_ind_arity|];[|val_pol_arity|]|]

let val_one_ind = val_tuple "one_ind"
  [|val_id;val_rctxt;val_ind_arity;val_array val_id;val_array val_constr;
    val_int; val_list val_sortfam;val_array val_constr;val_array val_int;
    val_wfp; val_int; val_int; no_val|]

let val_ind_pack = val_tuple "ind_pack"
  [|val_array val_one_ind;val_bool;val_bool;val_int;val_nctxt;
    val_int; val_int; val_rctxt;val_cstrs;val_opt val_kn|]

let rec val_sfb o = val_sum "sfb" 0
  [|[|val_cb|];[|val_ind_pack|];[|val_mod|];
    [|val_mp;val_opt val_cstrs|];[|val_modty|]|] o
and val_sb o = val_list (val_tuple"sb"[|val_id;val_sfb|]) o
and val_seb o = val_sum "seb" 0
  [|[|val_mp|];[|val_uid;val_modty;val_seb|];[|val_uid;val_sb|];
    [|val_seb;val_seb;val_cstrs|];[|val_seb;val_with|]|] o
and val_with o = val_sum "with" 0
  [|[|val_list val_id;val_mp;val_cstrs|];
    [|val_list val_id;val_cb|]|] o
and val_mod o = val_tuple "module_body"
  [|val_opt val_seb;val_opt val_seb;val_cstrs;val_subst;no_val|] o
and val_modty o = val_tuple "module_type_body"
  [|val_seb;val_opt val_mp;val_subst|] o

let val_deps = val_list (val_tuple"dep"[|val_dp;no_val|])

let val_vo = val_tuple "vo" [|val_dp;val_mod;val_deps;val_eng|]
