
(* $Id$ *)

open Names
open Util
open Generic
open Term

(* Signatures *)

type 'a signature = identifier list * 'a list
type 'a db_signature = (name * 'a) list
type ('a,'b) env = ENVIRON of 'a signature * 'b db_signature

let gLOB hyps = ENVIRON (hyps,[])

let ids_of_sign (idl,_) = idl
let vals_of_sign (_,vals) = vals
let add_sign (id,ty) (idl,tyl) = (id::idl,ty::tyl)
let sign_it f (idl,tyl) e = List.fold_right2 f idl tyl e
let it_sign f e (idl,tyl) = List.fold_left2 f e idl tyl
let nil_sign = ([],[])
let rev_sign (idl,tyl) = (List.rev idl, List.rev tyl)
let map_sign_typ f (idl,tyl) = (idl, List.map f tyl)
let concat_sign (idl1,tyl1) (idl2,tyl2) = (idl1@idl2, tyl1@tyl2)
let diff_sign (idl1,tyl1) (idl2,tyl2) = 
  (subtract idl1 idl2, subtract tyl1 tyl2)
let nth_sign (idl,tyl) n = (List.nth idl (n-1), List.nth tyl (n-1))
let map_sign_graph f (ids,tys) = List.map2 f ids tys

let isnull_sign = function 
  | ([],[])     -> true
  | (_::_,_::_) -> false
  | _           -> invalid_arg "isnull_sign"

let hd_sign = function
  | (id::_,ty::_) -> (id,ty)
  | _             -> failwith "hd_sign"

let tl_sign = function
  | (_::idl,_::tyl) -> (idl,tyl)
  | _               -> failwith "tl_sign"

let lookup_sign id (dom,rang) = 
  let rec aux = function
    | ([],          [])        -> raise Not_found
    | ((id'::id'l), (ty::tyl)) -> if id' = id then (id',ty) else aux (id'l,tyl)
    | _                        -> anomaly "Names: lookup_sign"
  in 
  aux (dom,rang)

let list_of_sign (ids,tys) =
  try List.combine ids tys
  with _ -> anomaly "Corrupted signature"

let make_sign = List.split
let do_sign f (ids,tys) = List.iter2 f ids tys

let uncons_sign = function
  | (id::idl,ty::tyl) -> ((id,ty),(idl,tyl))
  | _ -> anomaly "signatures are being manipulated in a non-abstract way"

let sign_length (idl,tyl) =
  let lenid = List.length idl
  and lenty = List.length tyl in
  if lenid = lenty then 
    lenid
  else 
    invalid_arg "lookup_sign"

let mem_sign sign id = List.mem id (ids_of_sign sign)

let modify_sign id ty = 
  let rec modrec = function
    | [],[] -> invalid_arg "modify_sign"
    | sign  -> 
	let (id',ty') = hd_sign sign in
	if id = id' then
      	  add_sign (id,ty) (tl_sign sign)
	else
      	  add_sign (id',ty') (modrec (tl_sign sign))
  in 
  modrec

let exists_sign f = 
  let rec exrec sign =
    if isnull_sign sign then 
      false
    else 
      let ((id,t),tl) = uncons_sign sign in
      f id t or exrec tl
  in 
  exrec

(* [sign_prefix id sign] returns the signature up to and including id,
   with all later assumptions stripped off.  It is an error to call it
   with a signature not containing id, and that error is generated
   with error. *)

let sign_prefix id sign = 
  let rec prefrec sign =
    if isnull_sign sign then
      error "sign_prefix"
    else
      let ((id',t),sign') = uncons_sign sign in
      if id' = id then sign else prefrec sign'
  in 
  prefrec sign

let add_sign_after whereid (id,t) sign = 
  let rec addrec sign =
    if isnull_sign sign then
      error "add_sign_after"
    else
      let ((id',t'),sign') = uncons_sign sign in
      if id' = whereid then add_sign (id,t) sign
      else add_sign (id',t') (addrec sign')
  in 
  addrec sign

let add_sign_replacing whereid (id,t) sign = 
  let rec addrec sign =
    if isnull_sign sign then
      error "add_replacing_after"
    else
      let ((id',t'),sign') = uncons_sign sign in
      if id' = whereid then add_sign (id,t) sign'
      else add_sign (id',t') (addrec sign')
  in 
  addrec sign
  
(* [prepend_sign Gamma1 Gamma2]
   prepends Gamma1 to the front of Gamma2, given that their namespaces
   are distinct. *)

let prepend_sign gamma1 gamma2 =
  if [] = intersect (ids_of_sign gamma1) (ids_of_sign gamma2) then
    let (ids1,vals1) = gamma1
    and (ids2,vals2) = gamma2 in
    (ids1@ids2, vals1@vals2)
  else
    invalid_arg "prepend_sign"

let dunbind default sign ty = function 
  | DLAM(na,c) ->
      let id = next_ident_away (id_of_name default na) (ids_of_sign sign) in
      (add_sign (id,ty) sign, subst1 (VAR id) c)
  | _ -> invalid_arg "dunbind default"

let dunbindv default sign ty = function
  | DLAMV(na,c) ->
      let id = next_ident_away (id_of_name default na) (ids_of_sign sign) in 
      (add_sign (id,ty) sign,Array.map (subst1 (VAR id)) c)
  | _ -> invalid_arg "dunbindv default"

let dbind sign c =
  let (id,ty) = hd_sign sign
  and sign' = tl_sign sign in
  (ty,DLAM(Name id,subst_var id c))

let dbindv sign cl =
  let (id,ty) = hd_sign sign
  and sign' = tl_sign sign in
  (ty,DLAMV(Name id,Array.map (subst_var id) cl))


(* Signatures + de Bruijn environments *)

let dbenv_it f (ENVIRON(_,dbs)) init =
  List.fold_right (fun (na,t) v -> f na t v) dbs init

let it_dbenv f init (ENVIRON(_,dbs)) =
  List.fold_left (fun v (na,t) -> f v na t) init dbs

let isnull_rel_env (ENVIRON(_,dbs)) = (dbs = [])
let uncons_rel_env (ENVIRON(sign,dbs)) = List.hd dbs,ENVIRON(sign,List.tl dbs)

let ids_of_env (ENVIRON(sign,dbenv)) =
  let filter (n,_) l = match n with (Name id) -> id::l | Anonymous -> l in
  (ids_of_sign sign) @ (List.fold_right filter dbenv [])

let get_globals (ENVIRON(g,_)) = g
let get_rels (ENVIRON(_,r)) = r

let add_rel (n,x) (ENVIRON(g,r)) = (ENVIRON(g,(n,x)::r))

let add_glob (id,x) (ENVIRON((dom,rang),r)) = (ENVIRON((id::dom,x::rang),r))

let lookup_glob id (ENVIRON((dom,rang),_)) = 
  let rec aux = function
    | ([],          [])        -> raise Not_found
    | ((id'::id'l), (ty::tyl)) -> if id' = id then (id',ty) else aux (id'l,tyl)
    | _                        -> anomaly "Names: lookup_glob"
  in 
  aux (dom,rang)

let mem_glob id (ENVIRON((dom,_),_)) = List.mem id dom

let lookup_rel n (ENVIRON(_,r)) = 
  let rec lookrec n l = match (n,l) with
    | (1, ((na,x)::l)) -> (na,x)
    | (n, (_::l))      -> lookrec (n-1) l
    | (_, [])          -> raise Not_found
  in 
  lookrec n r

let rec lookup_rel_id id (ENVIRON(_,r)) = 
  let rec lookrec = function
    | (n, ((Anonymous,x)::l)) -> lookrec (n+1,l)
    | (n, ((Name id',x)::l))  -> if id' = id then (n,x) else lookrec (n+1,l)
    | (_, [])                 -> raise Not_found
  in 
  lookrec (1,r)

let map_rel_env f (ENVIRON(g,r)) =
  ENVIRON (g,List.map (fun (na,x) -> (na,f x)) r)

let map_var_env f (ENVIRON((dom,rang),r)) =
  ENVIRON (List.fold_right2 
	     (fun na x (doml,rangl) -> (na::doml,(f x)::rangl))
      	     dom rang ([],[]),r)


type ('b,'a) search_result =
  | GLOBNAME of identifier  * 'b
  | RELNAME of int * 'a

let lookup_id id env =
  try 
    let (x,y) = lookup_rel_id id env in RELNAME(x,y)
  with 
    | Not_found -> let (x,y) = lookup_glob id env in GLOBNAME(x,y)


type 'b assumptions = (typed_type,'b) env
type environment = (typed_type,typed_type) env
type context = typed_type signature

