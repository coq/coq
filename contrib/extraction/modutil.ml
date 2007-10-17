(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Declarations
open Environ
open Libnames
open Util
open Miniml
open Table
open Mlutil
open Mod_subst

(*S Functions upon modules missing in [Modops]. *) 

(*s Add _all_ direct subobjects of a module, not only those exported. 
   Build on the [Modops.add_signature] model. *)

let add_structure mp msb env = 
  let add_one env (l,elem) = 
    let kn = make_kn mp empty_dirpath l in 
    let con = make_con mp empty_dirpath l in 
    match elem with 
      | SEBconst cb -> Environ.add_constant con cb env 
      | SEBmind mib -> Environ.add_mind kn mib env 
      | SEBmodule mb -> Modops.add_module (MPdot (mp,l)) mb env 
      | SEBmodtype mtb -> Environ.add_modtype kn mtb env  
  in List.fold_left add_one env msb

(*s Apply a module path substitution on a module.
   Build on the [Modops.subst_modtype] model. *)

let rec subst_module sub mb =
  let mtb' = Modops.subst_modtype sub mb.mod_type
  and meb' = option_smartmap (subst_meb sub) mb.mod_expr
  and mtb'' = option_smartmap (Modops.subst_modtype sub) mb.mod_user_type
  and mpo' = option_smartmap (subst_mp sub) mb.mod_equiv in
  if (mtb'==mb.mod_type) && (meb'==mb.mod_expr) && 
    (mtb''==mb.mod_user_type) && (mpo'==mb.mod_equiv)
  then mb
  else { mod_expr= meb'; 
	 mod_type=mtb'; 
	 mod_user_type=mtb''; 
	 mod_equiv=mpo'; 
	 mod_constraints=mb.mod_constraints;
         mod_retroknowledge=[] } (* spiwack: since I'm lazy and it's unused at 
				    this point. I forget about retroknowledge, 
				    this may need a change later *)

and subst_meb sub = function 
  | MEBident mp -> MEBident (subst_mp sub mp) 
  | MEBfunctor (mbid, mtb, meb) -> 
      assert (not (occur_mbid mbid sub)); 
      MEBfunctor (mbid, Modops.subst_modtype sub mtb, subst_meb sub meb)
  | MEBstruct (msid, msb) -> 
      assert (not (occur_msid msid sub));
      MEBstruct (msid, subst_msb sub msb)
  | MEBapply (meb, meb', c) -> 
      MEBapply (subst_meb sub meb, subst_meb sub meb', c)

and subst_msb sub msb = 
  let subst_body = function
    | SEBconst cb -> SEBconst (subst_const_body sub cb)
    | SEBmind mib -> SEBmind (subst_mind sub mib)
    | SEBmodule mb -> SEBmodule (subst_module sub mb)
    | SEBmodtype mtb -> SEBmodtype (Modops.subst_modtype sub mtb)
  in List.map (fun (l,b) -> (l,subst_body b)) msb

(*s Change a msid in a module type, to follow a module expr. 
  Because of the "with" construct, the module type of a module can be a 
  [MTBsig] with a msid different from the one of the module. *)

let rec replicate_msid meb mtb = match meb,mtb with 
  | MEBfunctor (_, _, meb), MTBfunsig (mbid, mtb1, mtb2) -> 
      let mtb' = replicate_msid meb mtb2 in 
      if mtb' == mtb2 then mtb else MTBfunsig (mbid, mtb1, mtb')
  | MEBstruct (msid, _), MTBsig (msid1, msig) when msid <> msid1 -> 
      let msig' = Modops.subst_signature_msid msid1 (MPself msid) msig in
      if msig' == msig then MTBsig (msid, msig) else MTBsig (msid, msig')
  | _ -> mtb

(*S Functions upon ML modules. *)

(*s Apply some functions upon all [ml_decl] and [ml_spec] found in a 
   [ml_structure]. *) 

let struct_iter do_decl do_spec s = 
  let rec mt_iter = function 
    | MTident _ -> () 
    | MTfunsig (_,mt,mt') -> mt_iter mt; mt_iter mt'
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
	 | Equiv kne -> do_type (IndRef (kne, snd ip)); 
	 | _ -> ()); 
    Array.iteri (fun j -> cons_iter (ip,j+1)) p.ip_types 
  in
  if lang () = Ocaml then record_iter_references do_term ind.ind_info; 
  Array.iteri (fun i -> packet_iter (kn,i)) ind.ind_packets
  
let decl_iter_references do_term do_cons do_type = 
  let type_iter = type_iter_references do_type 
  and ast_iter = ast_iter_references do_term do_cons do_type in
  function 
    | Dind (kn,ind) -> ind_iter_references do_term do_cons do_type kn ind 
    | Dtype (r,_,t) -> do_type r; type_iter t 
    | Dterm (r,a,t) -> do_term r; ast_iter a; type_iter t
    | Dfix(rv,c,t) -> 	
	Array.iter do_term rv; Array.iter ast_iter c; Array.iter type_iter t

let spec_iter_references do_term do_cons do_type = function 
  | Sind (kn,ind) -> ind_iter_references do_term do_cons do_type kn ind
  | Stype (r,_,ot) -> do_type r; option_iter (type_iter_references do_type) ot
  | Sval (r,t) -> do_term r; type_iter_references do_type t

let struct_iter_references do_term do_cons do_type = 
  struct_iter 
    (decl_iter_references do_term do_cons do_type) 
    (spec_iter_references do_term do_cons do_type) 

(*s Get all references used in one [ml_structure], either in [list] or [set]. *)

type 'a kinds = { mutable typ : 'a ; mutable trm : 'a; mutable cons : 'a }

let struct_get_references empty add struc = 
  let o = { typ = empty ; trm = empty ; cons = empty } in 
  let do_type r = o.typ <- add r o.typ in 
  let do_term r = o.trm <- add r o.trm in
  let do_cons r = o.cons <- add r o.cons in 
  struct_iter_references do_term do_cons do_type struc; o

let struct_get_references_set = struct_get_references Refset.empty Refset.add

module Orefset = struct 
  type t = { set : Refset.t ; list : global_reference list }
  let empty = { set = Refset.empty ; list = [] }
  let add r o = 
    if Refset.mem r o.set then o 
    else { set = Refset.add r o.set ; list = r :: o.list }
  let set o = o.set
  let list o = o.list
end

let struct_get_references_list struc = 
  let o = struct_get_references Orefset.empty Orefset.add struc in 
  { typ = Orefset.list o.typ; 
    trm = Orefset.list o.trm; 
    cons = Orefset.list o.cons }


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
  | Stype (_,_,ot) -> option_iter (type_search f) ot
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
  with Not_found -> assert false


(*s Optimization of a [ml_structure]. *)

(* Some transformations of ML terms. [optimize_struct] simplify
   all beta redexes (when the argument does not occur, it is just
   thrown away; when it occurs exactly once it is substituted; otherwise
   a let-in redex is created for clarity) and iota redexes, plus some other
   optimizations. *)

let dfix_to_mlfix rv av i = 
  let rec make_subst n s = 
    if n < 0 then s 
    else make_subst (n-1) (Refmap.add rv.(n) (n+1) s)
  in 
  let s = make_subst (Array.length rv - 1) Refmap.empty 
  in 
  let rec subst n t = match t with 
    | MLglob ((ConstRef kn) as refe) -> 
	(try MLrel (n + (Refmap.find refe s)) with Not_found -> t)
    | _ -> ast_map_lift subst n t 
  in 
  let ids = Array.map (fun r -> id_of_label (label_of_r r)) rv in 
  let c = Array.map (subst 0) av 
  in MLfix(i, ids, c)

let rec optim to_appear s = function
  | [] -> []
  | (Dtype (r,_,Tdummy _) | Dterm(r,MLdummy,_)) as d :: l ->
      if List.mem r to_appear 
      then d :: (optim to_appear s l) 
      else optim to_appear s l
  | Dterm (r,t,typ) :: l ->
      let t = normalize (ast_glob_subst !s t) in 
      let i = inline r t in 
      if i then s := Refmap.add r t !s; 
      if not i || modular () || List.mem r to_appear 
      then 
	let d = match optimize_fix t with 
	  | MLfix (0, _, [|c|]) -> 
	      Dfix ([|r|], [|ast_subst (MLglob r) c|], [|typ|])
	  | t -> Dterm (r, t, typ)
	in d :: (optim to_appear s l)
      else optim to_appear s l
  | d :: l -> d :: (optim to_appear s l)

let rec optim_se top to_appear s = function 
  | [] -> [] 
  | (l,SEdecl (Dterm (r,a,t))) :: lse -> 
      let a = normalize (ast_glob_subst !s a) in 
      let i = inline r a in 
      if i then s := Refmap.add r a !s; 
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
	then s := Refmap.add rv.(i) (dfix_to_mlfix rv av i) !s
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

let optimize_struct to_appear struc = 
  let subst = ref (Refmap.empty : ml_ast Refmap.t) in 
  List.map (fun (mp,lse) -> (mp, optim_se true to_appear subst lse)) struc
