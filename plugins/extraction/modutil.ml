(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Declarations
open Environ
open Libnames
open Util
open Miniml
open Table
open Mlutil
open Mod_subst

(*S Functions upon ML modules. *)

let rec msid_of_mt = function
  | MTident mp -> mp
  | MTwith(mt,_)-> msid_of_mt mt
  | _ -> anomaly "Extraction:the With operator isn't applied to a name"

(*s Apply some functions upon all [ml_decl] and [ml_spec] found in a
   [ml_structure]. *)

let struct_iter do_decl do_spec s =
  let rec mt_iter = function
    | MTident _ -> ()
    | MTfunsig (_,mt,mt') -> mt_iter mt; mt_iter mt'
    | MTwith (mt,ML_With_type(idl,l,t))->
	let mp_mt = msid_of_mt mt in
	let l',idl' = list_sep_last idl in
	let mp_w =
	  List.fold_left (fun mp l -> MPdot(mp,label_of_id l)) mp_mt idl'
	in
	let r = ConstRef (make_con mp_w empty_dirpath (label_of_id l')) in
	mt_iter mt; do_decl (Dtype(r,l,t))
    | MTwith (mt,_)->mt_iter mt
    | MTsig (_, sign) -> List.iter spec_iter sign
  and spec_iter = function
    | (_,Spec s) -> do_spec s
    | (_,Smodule mt) -> mt_iter mt
    | (_,Smodtype mt) -> mt_iter mt
  in
  let rec se_iter = function
    | (_,SEdecl d) -> do_decl d
    | (_,SEmodule m) ->
	me_iter m.ml_mod_expr; mt_iter m.ml_mod_type
    | (_,SEmodtype m) -> mt_iter m
  and me_iter = function
    | MEident _ -> ()
    | MEfunctor (_,mt,me) -> me_iter me; mt_iter mt
    | MEapply (me,me') -> me_iter me; me_iter me'
    | MEstruct (msid, sel) -> List.iter se_iter sel
  in
  List.iter (function (_,sel) -> List.iter se_iter sel) s

(*s Apply some fonctions upon all references in [ml_type], [ml_ast],
  [ml_decl], [ml_spec] and [ml_structure]. *)

type do_ref = global_reference -> unit

let record_iter_references do_term = function
  | Record l -> List.iter do_term l
  | _ -> ()

let type_iter_references do_type t =
  let rec iter = function
    | Tglob (r,l) -> do_type r; List.iter iter l
    | Tarr (a,b) -> iter a; iter b
    | _ -> ()
  in iter t

let ast_iter_references do_term do_cons do_type a =
  let rec iter a =
    ast_iter iter a;
    match a with
      | MLglob r -> do_term r
      | MLcons (i,r,_) ->
	  if lang () = Ocaml then record_iter_references do_term i;
	  do_cons r
      | MLcase (i,_,v) ->
	  if lang () = Ocaml then record_iter_references do_term (fst i);
	  Array.iter (fun (r,_,_) -> do_cons r) v
      | _ -> ()
  in iter a

let ind_iter_references do_term do_cons do_type kn ind =
  let type_iter = type_iter_references do_type in
  let cons_iter cp l = do_cons (ConstructRef cp); List.iter type_iter l in
  let packet_iter ip p =
    do_type (IndRef ip);
    if lang () = Ocaml then
      (match ind.ind_equiv with
	 | Miniml.Equiv kne -> do_type (IndRef (mind_of_kn kne, snd ip));
	 | _ -> ());
    Array.iteri (fun j -> cons_iter (ip,j+1)) p.ip_types
  in
  if lang () = Ocaml then record_iter_references do_term ind.ind_info;
    Array.iteri (fun i -> packet_iter (kn,i)) ind.ind_packets

let decl_iter_references do_term do_cons do_type =
  let type_iter = type_iter_references do_type
  and ast_iter = ast_iter_references do_term do_cons do_type in
  function
    | Dind (kn,ind) -> ind_iter_references do_term do_cons do_type 
	(mind_of_kn kn) ind
    | Dtype (r,_,t) -> do_type r; type_iter t
    | Dterm (r,a,t) -> do_term r; ast_iter a; type_iter t
    | Dfix(rv,c,t) ->
	Array.iter do_term rv; Array.iter ast_iter c; Array.iter type_iter t

let spec_iter_references do_term do_cons do_type = function
  | Sind (kn,ind) -> ind_iter_references do_term do_cons do_type (mind_of_kn kn) ind
  | Stype (r,_,ot) -> do_type r; Option.iter (type_iter_references do_type) ot
  | Sval (r,t) -> do_term r; type_iter_references do_type t

(*s Searching occurrences of a particular term (no lifting done). *)

exception Found

let rec ast_search f a =
  if f a then raise Found else ast_iter (ast_search f) a

let decl_ast_search f = function
  | Dterm (_,a,_) -> ast_search f a
  | Dfix (_,c,_) -> Array.iter (ast_search f) c
  | _ -> ()

let struct_ast_search f s =
  try struct_iter (decl_ast_search f) (fun _ -> ()) s; false
  with Found -> true

let rec type_search f = function
  | Tarr (a,b) -> type_search f a; type_search f b
  | Tglob (r,l) -> List.iter (type_search f) l
  | u -> if f u then raise Found

let decl_type_search f = function
  | Dind (_,{ind_packets=p})  ->
      Array.iter
	(fun {ip_types=v} -> Array.iter (List.iter (type_search f)) v) p
  | Dterm (_,_,u) -> type_search f u
  | Dfix (_,_,v) -> Array.iter (type_search f) v
  | Dtype (_,_,u) -> type_search f u

let spec_type_search f = function
  | Sind (_,{ind_packets=p}) ->
      Array.iter
	(fun {ip_types=v} -> Array.iter (List.iter (type_search f)) v) p
  | Stype (_,_,ot) -> Option.iter (type_search f) ot
  | Sval (_,u) -> type_search f u

let struct_type_search f s =
  try struct_iter (decl_type_search f) (spec_type_search f) s; false
  with Found -> true


(*s Generating the signature. *)

let rec msig_of_ms = function
  | [] -> []
  | (l,SEdecl (Dind (kn,i))) :: ms ->
      (l,Spec (Sind (kn,i))) :: (msig_of_ms ms)
  | (l,SEdecl (Dterm (r,_,t))) :: ms ->
      (l,Spec (Sval (r,t))) :: (msig_of_ms ms)
  | (l,SEdecl (Dtype (r,v,t))) :: ms ->
      (l,Spec (Stype (r,v,Some t))) :: (msig_of_ms ms)
  | (l,SEdecl (Dfix (rv,_,tv))) :: ms ->
      let msig = ref (msig_of_ms ms) in
      for i = Array.length rv - 1 downto 0 do
	msig := (l,Spec (Sval (rv.(i),tv.(i))))::!msig
      done;
      !msig
  | (l,SEmodule m) :: ms -> (l,Smodule m.ml_mod_type) :: (msig_of_ms ms)
  | (l,SEmodtype m) :: ms -> (l,Smodtype m) :: (msig_of_ms ms)

let signature_of_structure s =
  List.map (fun (mp,ms) -> mp,msig_of_ms ms) s


(*s Searching one [ml_decl] in a [ml_structure] by its [global_reference] *)

let get_decl_in_structure r struc =
  try
    let base_mp,ll = labels_of_ref r in
    if not (at_toplevel base_mp) then error_not_visible r;
    let sel = List.assoc base_mp struc in
    let rec go ll sel = match ll with
      | [] -> assert false
      | l :: ll ->
	  match List.assoc l sel with
	    | SEdecl d -> d
	    | SEmodtype m -> assert false
	    | SEmodule m ->
		match m.ml_mod_expr with
		  | MEstruct (_,sel) -> go ll sel
		  | _ -> error_not_visible r
    in go ll sel
  with Not_found ->
    anomaly "reference not found in extracted structure"


(*s Optimization of a [ml_structure]. *)

(* Some transformations of ML terms. [optimize_struct] simplify
   all beta redexes (when the argument does not occur, it is just
   thrown away; when it occurs exactly once it is substituted; otherwise
   a let-in redex is created for clarity) and iota redexes, plus some other
   optimizations. *)

let dfix_to_mlfix rv av i =
  let rec make_subst n s =
    if n < 0 then s
    else make_subst (n-1) (Refmap'.add rv.(n) (n+1) s)
  in
  let s = make_subst (Array.length rv - 1) Refmap'.empty
  in
  let rec subst n t = match t with
    | MLglob ((ConstRef kn) as refe) ->
	(try MLrel (n + (Refmap'.find refe s)) with Not_found -> t)
    | _ -> ast_map_lift subst n t
  in
  let ids = Array.map (fun r -> id_of_label (label_of_r r)) rv in
  let c = Array.map (subst 0) av
  in MLfix(i, ids, c)

let rec optim_se top to_appear s = function
  | [] -> []
  | (l,SEdecl (Dterm (r,a,t))) :: lse ->
      let a = normalize (ast_glob_subst !s a) in
      let i = inline r a in
      if i then s := Refmap'.add r a !s;
      if top && i && not (modular ()) && not (List.mem r to_appear)
      then optim_se top to_appear s lse
      else
	let d = match optimize_fix a with
	  | MLfix (0, _, [|c|]) ->
	      Dfix ([|r|], [|ast_subst (MLglob r) c|], [|t|])
	  | a -> Dterm (r, a, t)
	in (l,SEdecl d) :: (optim_se top to_appear s lse)
  | (l,SEdecl (Dfix (rv,av,tv))) :: lse ->
      let av = Array.map (fun a -> normalize (ast_glob_subst !s a)) av in
      let all = ref true in
      (* This fake body ensures that no fixpoint will be auto-inlined. *)
      let fake_body = MLfix (0,[||],[||]) in
      for i = 0 to Array.length rv - 1 do
	if inline rv.(i) fake_body
	then s := Refmap'.add rv.(i) (dfix_to_mlfix rv av i) !s
	else all := false
      done;
      if !all && top && not (modular ())
	&& (array_for_all (fun r -> not (List.mem r to_appear)) rv)
      then optim_se top to_appear s lse
      else (l,SEdecl (Dfix (rv, av, tv))) :: (optim_se top to_appear s lse)
  | (l,SEmodule m) :: lse ->
      let m = { m with ml_mod_expr = optim_me to_appear s m.ml_mod_expr}
      in (l,SEmodule m) :: (optim_se top to_appear s lse)
  | se :: lse -> se :: (optim_se top to_appear s lse)

and optim_me to_appear s = function
  | MEstruct (msid, lse) -> MEstruct (msid, optim_se false to_appear s lse)
  | MEident mp as me -> me
  | MEapply (me, me') ->
      MEapply (optim_me to_appear s me, optim_me to_appear s me')
  | MEfunctor (mbid,mt,me) -> MEfunctor (mbid,mt, optim_me to_appear s me)

(* After these optimisations, some dependencies may not be needed anymore.
   For monolithic extraction, we recompute a minimal set of dependencies. *)

exception NoDepCheck

let base_r = function
  | ConstRef c as r -> r
  | IndRef (kn,_) -> IndRef (kn,0)
  | ConstructRef ((kn,_),_) -> IndRef (kn,0)
  | _ -> assert false

let reset_needed, add_needed, found_needed, is_needed =
  let needed = ref Refset'.empty in
  ((fun l -> needed := Refset'.empty),
   (fun r -> needed := Refset'.add (base_r r) !needed),
   (fun r -> needed := Refset'.remove (base_r r) !needed),
   (fun r -> Refset'.mem (base_r r) !needed))

let declared_refs = function
  | Dind (kn,_) -> [|IndRef (mind_of_kn kn,0)|]
  | Dtype (r,_,_) -> [|r|]
  | Dterm (r,_,_) -> [|r|]
  | Dfix (rv,_,_) -> rv

(* Computes the dependencies of a declaration, except in case
   of custom extraction. *)

let compute_deps_decl = function
  | Dind (kn,ind) ->
      (* Todo Later : avoid dependencies when Extract Inductive *)
      ind_iter_references add_needed add_needed add_needed (mind_of_kn kn) ind
  | Dtype (r,ids,t) ->
      if not (is_custom r) then type_iter_references add_needed t
  | Dterm (r,u,t) ->
      type_iter_references add_needed t;
      if not (is_custom r) then
	ast_iter_references add_needed add_needed add_needed u
  | Dfix _ as d ->
      (* Todo Later : avoid dependencies when Extract Constant *)
      decl_iter_references add_needed add_needed add_needed d

let rec depcheck_se = function
  | [] -> []
  | ((l,SEdecl d) as t)::se ->
      let se' = depcheck_se se in
      let rv = declared_refs d in
      if not (array_exists is_needed rv) then
	(Array.iter remove_info_axiom rv; se')
      else
	(Array.iter found_needed rv; compute_deps_decl d; t::se')
  | _ -> raise NoDepCheck

let rec depcheck_struct = function
  | [] -> []
  | (mp,lse)::struc ->
      let struc' = depcheck_struct struc in
      let lse' = depcheck_se lse in
      (mp,lse')::struc'

let check_implicits = function
  | MLexn s ->
      if String.length s > 8 && (s.[0] = 'U' || s.[0] = 'I') then
	begin
	  if String.sub s 0 7 = "UNBOUND" then assert false;
	  if String.sub s 0 8 = "IMPLICIT" then
	    error_non_implicit (String.sub s 9 (String.length s - 9));
	end;
      false
  | _ -> false

let optimize_struct to_appear struc =
  let subst = ref (Refmap'.empty : ml_ast Refmap'.t) in
  let opt_struc =
    List.map (fun (mp,lse) -> (mp, optim_se true to_appear subst lse)) struc
  in
  let opt_struc = List.filter (fun (_,lse) -> lse<>[]) opt_struc in
  ignore (struct_ast_search check_implicits opt_struc);
  try
    if modular () then raise NoDepCheck;
    reset_needed ();
    List.iter add_needed to_appear;
    depcheck_struct opt_struc
  with NoDepCheck -> opt_struc
