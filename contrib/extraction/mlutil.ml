
open Util
open Miniml

(*s [occurs : int -> ml_ast -> bool]
    [occurs k M] returns true if (Rel k) occurs in M. *)

let rec occurs k = function
  | MLrel i          -> i=k
  | MLapp(t,argl)    -> (occurs k t) or (occurs_list k argl)
  | MLlam(_,t)       -> occurs (k+1) t
  | MLcons(_,_,argl) -> occurs_list k argl
  | MLcase(t,pv)     -> 
      (occurs k t) or
      (List.exists (fun (k',t') -> occurs (k+k') t')
      	 (array_map_to_list (fun (_,l,t') -> 
      	       	           let k' = List.length l in (k',t')) pv))
  | MLfix(_,l,cl)  -> let k' = List.length l in occurs_list (k+k') cl
  | _                -> false

and occurs_list k l =
  List.exists (fun t -> occurs k t) l

(*s map over ML asts *)

let rec ast_map f = function
  | MLapp (a,al) -> MLapp (f a, List.map f al)
  | MLlam (id,a) -> MLlam (id, f a)
  | MLletin (id,a,b) -> MLletin (id, f a, f b)
  | MLcons (c,n,al)  -> MLcons (c, n, List.map f al)
  | MLcase (a,eqv) -> MLcase (f a, Array.map (ast_map_eqn f) eqv)
  | MLfix (fi,ids,al) -> MLfix (fi, ids, List.map f al)
  | MLcast (a,t) -> MLcast (f a, t)
  | MLmagic a -> MLmagic (f a)
  | a -> a

and ast_map_eqn f (c,ids,a) = (c,ids,f a)

(*s Lifting on terms [ml_lift : int -> ml_ast -> ml_ast]
    [ml_lift k M] lifts the binding depth of [M] across [k] bindings. *)

let ml_liftn k n c = 
  let rec liftrec n = function
    | MLrel i as c -> if i < n then c else MLrel (i+k)
    | MLlam (id,t) -> MLlam (id, liftrec (n+1) t)
    | MLletin (id,a,b) -> MLletin (id, liftrec n a, liftrec (n+1) b)
    | MLcase(t,pl) -> 
	MLcase (liftrec n t,
      	       	Array.map (fun (id,idl,p) -> 
			     let k = List.length idl in
			     (id, idl, liftrec (n+k) p)) pl)
    | MLfix (n0,idl,pl) -> 
	MLfix (n0,idl,
	       let k = List.length idl in List.map (liftrec (n+k)) pl)
    | a -> ast_map (liftrec n) a
  in 
  if k = 0 then c else liftrec n c

let ml_lift k c = ml_liftn k 1 c

let pop c = ml_lift (-1) c

(*s [uncurrify] uncurrifies the applications of constructors *)

let rec is_constructor_app = function
  | MLcons _ -> true
  | MLapp (a,_) -> is_constructor_app a
  | _ -> false

let rec decomp_app = function
  | MLapp (f,args) -> 
      let (c,n,args') = decomp_app f in (c, n, args' @ args)
  | MLcons (c,n,args) ->
      (c,n,args)
  | _ ->
      assert false

let anonymous = Names.id_of_string "x"

let rec n_lam n a =
  if n = 0 then a else MLlam (anonymous, n_lam (pred n) a)

let eta_expanse c n args =
  let dif = n - List.length args in
  assert (dif >= 0);
  if dif > 0 then
    let rels = List.rev_map (fun n -> MLrel n) (interval 1 dif) in
    n_lam dif (MLcons (c, n, (List.map (ml_lift dif) args) @ rels))
  else
    MLcons (c,n,args)

let rec uncurrify_ast a = match a with
  | MLapp (f,_) when is_constructor_app f -> 
      let (c,n,args) = decomp_app a in
      let args' = List.map uncurrify_ast args in
      eta_expanse c n args'
  | MLcons (c,n,args) ->
      let args' = List.map uncurrify_ast args in
      eta_expanse c n args'
  | _ -> 
      ast_map uncurrify_ast a

let uncurrify_decl = function
 | Dglob (id, a) -> Dglob (id, uncurrify_ast a)
 | d -> d

