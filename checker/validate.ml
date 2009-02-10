(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: term.ml 10098 2007-08-27 11:41:08Z herbelin $ *)

(* This module defines validation functions to ensure an imported
   value (using input_value) has the correct structure. *)

let rec pr_obj_rec o =
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
        pr_obj_rec (Obj.field o i);
        if i<>n-1 then (Format.print_string ","; Format.print_cut())
      done;
      Format.close_box();
      Format.print_string ")")
  else Format.print_string "?"

let pr_obj o = pr_obj_rec o; Format.print_newline()

(**************************************************************************)
(* Low-level validators *)

(* data not validated *)
let no_val (o:Obj.t) = ()

(* Check that object o is a block with tag t *)
let val_tag t o =
  if Obj.is_block o && Obj.tag o = t then ()
  else failwith ("tag "^string_of_int t)

let val_obj s o =
  if Obj.is_block o then
    (if Obj.tag o > Obj.no_scan_tag then
      failwith (s^". Not a normal tag"))
  else failwith (s^". Not a block")

(* Check that an object is a tuple (or a record). v is an array of
   validation functions for each field. Its size corresponds to the
   expected size of the object. *)
let val_tuple s v o =
  let n = Array.length v in
  val_obj ("tuple: "^s) o;
  if Obj.size o = n then
    Array.iteri (fun i f -> f (Obj.field o i)) v
  else
    (pr_obj o;
     failwith
       ("tuple:" ^s^" size found:"^string_of_int (Obj.size o)))

(* Check that the object is either a constant constructor of tag < cc,
   or a constructed variant. each element of vv is an array of
   validation functions to be applied to the constructor arguments.
   The size of vv corresponds to the number of non-constant
   constructors, and the size of vv.(i) is the expected arity of the
   i-th non-constant constructor. *)
let val_sum s cc vv o =
  if Obj.is_block o then
    (val_obj ("sum: "^s) o;
    let n = Array.length vv in
    let i = Obj.tag o in
    if i < n then val_tuple (s^"("^string_of_int i^")") vv.(i) o
    else failwith ("bad tag in sum ("^s^"): "^string_of_int i))
  else if Obj.is_int o then
    let (n:int) = Obj.magic o in
    (if n<0 || n>=cc then failwith ("bad constant constructor ("^s^")"))
  else failwith ("not a sum ("^s^")")

let val_enum s n = val_sum s n [||]

(* Recursive types: avoid looping by eta-expansion *)
let rec val_rec_sum s cc f o =
  val_sum s cc (f (val_rec_sum s cc f)) o

(**************************************************************************)
(* Builtin types *)

(* Check the o is an array of values satisfying f. *)
let val_array f o =
  val_obj "array" o;
  for i = 0 to Obj.size o - 1 do
    (f (Obj.field o i):unit)
  done

(* Integer validator *)
let val_int o =
  if not (Obj.is_int o) then failwith "expected an int"

(* String validator *)
let val_str s = val_tag Obj.string_tag s

(* Booleans *)
let val_bool = val_enum "bool" 2

(* Option type *)
let val_opt f = val_sum "option" 1 [|[|f|]|]

(* Lists *)
let val_list f =
  val_rec_sum "list" 1 (fun vlist -> [|[|f;vlist|]|])

(* Reference *)
let val_ref f = val_tuple "ref" [|f|]

(**************************************************************************)
(* Standard library types *)

(* Sets *)
let val_set f =
  val_rec_sum "set" 1 (fun vset -> [|[|vset;f;vset;val_int|]|])

(* Maps *)
let rec val_map fk fv =
  val_rec_sum "map" 1 (fun vmap -> [|[|vmap;fk;fv;vmap;val_int|]|])

(**************************************************************************)
(* Coq types *)

let val_id = val_str

let val_dp = val_list val_id

let val_name = val_sum "name" 1 [|[|val_id|]|]

let val_uid = val_tuple "uid" [|val_int;val_str;val_dp|]

let val_mp =
  val_rec_sum "mp" 0
    (fun vmp -> [|[|val_dp|];[|val_uid|];[|val_uid|];[|vmp;val_id|]|])

let val_kn = val_tuple "kn" [|val_mp;val_dp;val_id|]

let val_ind = val_tuple "ind"[|val_kn;val_int|]
let val_cstr = val_tuple "cstr"[|val_ind;val_int|]

let val_ci =
  let val_cstyle = val_enum "case_style" 5 in
  let val_cprint = val_tuple "case_printing" [|val_int;val_cstyle|] in
  val_tuple "case_info" [|val_ind;val_int;val_array val_int;val_cprint|]


let val_level = val_sum "level" 1 [|[|val_dp;val_int|]|]
let val_univ = val_sum "univ" 0
  [|[|val_level|];[|val_list val_level;val_list val_level|]|]

let val_cstrs =
  val_set (val_tuple"univ_cstr"[|val_level;val_enum "order" 3;val_level|])

let val_cast = val_enum "cast_kind" 2
let val_sort = val_sum "sort" 0 [|[|val_enum "cnt" 2|];[|val_univ|]|]
let val_sortfam = val_enum "sort_family" 3

let val_evar f = val_tuple "evar" [|val_int;val_array f|]

let val_prec f =
  val_tuple "prec"[|val_array val_name; val_array f; val_array f|]
let val_fix f =
  val_tuple"fix1"[|val_tuple"fix2"[|val_array val_int;val_int|];val_prec f|]
let val_cofix f = val_tuple"cofix"[|val_int;val_prec f|]


let val_constr = val_rec_sum "constr" 0 (fun val_constr -> [|
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
|])


let val_ndecl = val_tuple"ndecl"[|val_id;val_opt val_constr;val_constr|]
let val_rdecl = val_tuple"rdecl"[|val_name;val_opt val_constr;val_constr|]
let val_nctxt = val_list val_ndecl
let val_rctxt = val_list val_rdecl

let val_arity = val_tuple"arity"[|val_rctxt;val_constr|]

let val_eng = val_enum "eng" 1

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

let val_wfp = val_rec_sum "wf_paths" 0
  (fun val_wfp -> 
    [|[|val_int;val_int|];[|val_recarg;val_array val_wfp|];
      [|val_int;val_array val_wfp|]|])

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
    [|val_mp;val_opt val_seb;val_opt val_cstrs|];[|val_modty|]|] o
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
