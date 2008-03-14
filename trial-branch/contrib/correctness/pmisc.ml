(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Libnames
open Topconstr

(* debug *)

let deb_mess s =
  if !Flags.debug then begin
    msgnl s; pp_flush()
  end

let deb_print f x =
  if !Flags.debug then begin
    msgnl (f x); pp_flush()
  end

let list_of_some = function
    None -> []
  | Some x -> [x]

let difference l1 l2 =
  let rec diff = function
      [] -> []
    | a::rem -> if List.mem a l2 then diff rem else a::(diff rem)
  in
    diff l1

(* TODO: these functions should be moved in the code of Coq *)

let reraise_with_loc loc f x =
  try f x with Util.UserError (_,_) as e -> Stdpp.raise_with_loc loc e


(* functions on names *)

let at = if !Flags.v7 then "@" else "'at'"

let at_id id d = id_of_string ((string_of_id id) ^ at ^ d)

let is_at id =
  try
    let _ = string_index_from (string_of_id id) 0 at in true
  with Not_found ->
    false

let un_at id =
  let s = string_of_id id in
    try
      let n = string_index_from s 0 at in
    	id_of_string (String.sub s 0 n),
	String.sub s (n + String.length at)
          (String.length s - n - String.length at)
    with Not_found ->
      invalid_arg "un_at"

let renaming_of_ids avoid ids =
  let rec rename avoid = function
      [] -> [], avoid
    | x::rem ->
	let al,avoid = rename avoid rem in
	let x' = next_ident_away x avoid in
	  (x,x')::al, x'::avoid
  in
    rename avoid ids

let result_id = id_of_string "result"

let adr_id id = id_of_string ("adr_" ^ (string_of_id id))

(* hypotheses names *)

let next s r = function
    Anonymous -> incr r; id_of_string (s ^ string_of_int !r)
  | Name id -> id

let reset_names,pre_name,post_name,inv_name,
    test_name,bool_name,var_name,phi_name,for_name,label_name =
  let pre = ref 0 in
  let post = ref 0 in
  let inv = ref 0 in
  let test = ref 0 in
  let bool = ref 0 in
  let var = ref 0 in
  let phi = ref 0 in
  let forr = ref 0 in
  let label = ref 0 in
    (fun () -> 
       pre := 0; post := 0; inv := 0; test := 0; 
       bool := 0; var := 0; phi := 0; label := 0),
    (next "Pre" pre),
    (next "Post" post),
    (next "Inv" inv),
    (next "Test" test),
    (fun () -> next "Bool" bool Anonymous),
    (next "Variant" var),
    (fun () -> next "rphi" phi Anonymous),
    (fun () -> next "for" forr Anonymous),
    (fun () -> string_of_id (next "Label" label Anonymous))

let default = id_of_string "x_"
let id_of_name = function Name id -> id | Anonymous -> default


(* functions on CIC terms *)

let isevar = Evarutil.new_evar_in_sign (Global.env ())

(* Substitutions of variables by others. *)
let subst_in_constr alist =
  let alist' = List.map (fun (id,id') -> (id, mkVar id')) alist in
  replace_vars alist'

(*
let subst_in_ast alist ast =
  let rec subst = function
      Nvar(l,s) -> Nvar(l,try List.assoc s alist with Not_found -> s)
    | Node(l,s,args) -> Node(l,s,List.map subst args)
    | Slam(l,so,a) -> Slam(l,so,subst a) (* TODO:enlever so de alist ? *)
    | x -> x
  in
    subst ast
*)
(*
let subst_ast_in_ast alist ast =
  let rec subst = function
      Nvar(l,s) as x -> (try List.assoc s alist with Not_found -> x)
    | Node(l,s,args) -> Node(l,s,List.map subst args)
    | Slam(l,so,a) -> Slam(l,so,subst a) (* TODO:enlever so de alist ? *)
    | x -> x
  in
    subst ast
*)

let rec subst_in_ast alist = function
  | CRef (Ident (loc,id)) ->
      CRef (Ident (loc,(try List.assoc id alist with Not_found -> id)))
  | x -> map_constr_expr_with_binders subst_in_ast List.remove_assoc alist x

let rec subst_ast_in_ast alist = function
  | CRef (Ident (_,id)) as x -> (try List.assoc id alist with Not_found -> x)
  | x ->
      map_constr_expr_with_binders subst_ast_in_ast List.remove_assoc alist x

(* subst. of variables by constr *)
let real_subst_in_constr = replace_vars

(* Coq constants *)

let coq_constant d s =
  Libnames.encode_kn
    (make_dirpath (List.rev (List.map id_of_string ("Coq"::d))))
    (id_of_string s)

let bool_sp = coq_constant ["Init"; "Datatypes"] "bool"
let coq_true = mkConstruct ((bool_sp,0),1)
let coq_false = mkConstruct ((bool_sp,0),2)

let constant s =
  let id = Constrextern.id_of_v7_string s in
  Constrintern.global_reference id

let connective_and = id_of_string "prog_bool_and"
let connective_or  = id_of_string "prog_bool_or"
let connective_not = id_of_string "prog_bool_not"

let is_connective id =
  id = connective_and or id = connective_or or id = connective_not

(* [conj i s] constructs the conjunction of two constr *)

let conj i s = Term.applist (constant "and", [i; s])

(* [n_mkNamedProd v [xn,tn;...;x1,t1]] constructs the type 
   [(x1:t1)...(xn:tn)v] *)

let rec n_mkNamedProd v = function
  | [] -> v
  | (id,ty) :: rem -> n_mkNamedProd (Term.mkNamedProd id ty v) rem

(* [n_lambda v [xn,tn;...;x1,t1]] constructs the type [x1:t1]...[xn:tn]v *)

let rec n_lambda v = function
  | [] -> v
  | (id,ty) :: rem -> n_lambda (Term.mkNamedLambda id ty v) rem

(* [abstract env idl c] constructs [x1]...[xn]c where idl = [x1;...;xn] *)

let abstract ids c = n_lambda c (List.rev ids)

(* substitutivity (of kernel names, for modules management) *)

open Ptype

let rec type_v_knsubst s = function
  | Ref v -> Ref (type_v_knsubst s v)
  | Array (c, v) -> Array (subst_mps s c, type_v_knsubst s v)
  | Arrow (bl, c) -> Arrow (List.map (binder_knsubst s) bl, type_c_knsubst s c)
  | TypePure c -> TypePure (subst_mps s c)

and type_c_knsubst s ((id,v),e,pl,q) =
  ((id, type_v_knsubst s v), e, 
   List.map (fun p -> { p with p_value = subst_mps s p.p_value }) pl,
   Option.map (fun q -> { q with a_value = subst_mps s q.a_value }) q)

and binder_knsubst s (id,b) = 
  (id, match b with BindType v -> BindType (type_v_knsubst s v) | _ -> b)
