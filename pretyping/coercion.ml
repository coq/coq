open Std;;
open Generic;;
open Names;;
open Term;;
open Reduction;;
open Himsg;;
open Machops;;
open Mach;;
open Classops;;
open Recordops;;
open Evarconv;;

(* Typing operations dealing with coercions *)

let class_of1 sigma t = class_of sigma (nf_ise1 sigma t);;

let j_nf_ise sigma {_VAL=v;_TYPE=t;_KIND=k} =
  {_VAL=nf_ise1 sigma v;_TYPE=nf_ise1 sigma t;_KIND=k}
let jl_nf_ise sigma = List.map (j_nf_ise sigma)

(* Here, funj is a coercion therefore already typed in global context *)
let apply_coercion_args argl funj =
  let rec apply_rec acc typ = function
      [] -> {_VAL=applist(j_val_only funj,argl);
             _TYPE= typ;
             _KIND = funj._KIND}
    | h::restl ->
 (* On devrait pouvoir s'arranger pour qu'on ait pas à faire hnf_constr *)
  match hnf_constr (Evd.mt_evd ()) typ with
     DOP2(Prod,c1,DLAM(_,c2)) -> (* Typage garanti par l'appel a app_coercion*)
       apply_rec (h::acc) (subst1 h c2) restl
    | _ -> anomaly "apply_coercion_args"
  in apply_rec [] funj._TYPE argl;;

(* appliquer le chemin de coercions p a` hj *)

let apply_pcoercion p hj typ_cl =
  if !compter then
    (nbpathc := !nbpathc +1; nbcoer := !nbcoer + (List.length p));
  try fst (List.fold_left
             (fun (ja,typ_cl) i -> 
                let fv,b= coe_value i in
                let argl = (class_args_of typ_cl)@[ja._VAL] in
                let jres = apply_coercion_args argl fv in
                  (if b then {_TYPE=jres._TYPE;_KIND=jres._KIND;_VAL=ja._VAL}
                   else jres),jres._TYPE)
             (hj,typ_cl) p)
  with _ -> failwith "apply_pcoercion"

let inh_app_fun isevars env j = 
 match whd_betadeltaiota !isevars j._TYPE with
    DOP2(Prod,_,DLAM(_,_)) -> j
   | _ ->
       (try
 	let t,i1 = class_of1 !isevars j._TYPE in
      	let p = lookup_path_to_fun_from i1 in
        apply_pcoercion p j t
      with _ -> j)
(* find out which exc we must trap (e.g we don't want to catch Sys.Break!) *)

let inh_tosort_force isevars env j =
  let t,i1 = class_of1 !isevars j._TYPE in
  let p = lookup_path_to_sort_from i1 in
  apply_pcoercion p j t 

let inh_tosort isevars env j = 
  let typ = whd_betadeltaiota !isevars j._TYPE in
  match typ with
    DOP0(Sort(_)) -> j  (* idem inh_app_fun *)
  | _ -> (try inh_tosort_force isevars env j with _ -> j)

let inh_ass_of_j isevars env j =
   let typ = whd_betadeltaiota !isevars j._TYPE in
     match typ with
         DOP0(Sort s) -> {body=j._VAL;typ=s}
       | _ ->
           (try
             let j1 = inh_tosort_force isevars env j
             in assumption_of_judgement !isevars env j1 
           with _ -> error_assumption CCI env (nf_ise1 !isevars j._VAL))
                   (* try ... with _ -> ... is BAD *)

let inh_coerce_to1 isevars env c1 v t k =
 let t1,i1 = class_of1 !isevars c1 in
 let t2,i2 = class_of1 !isevars t in
 let p = lookup_path_between (i2,i1) in
 let hj = {_VAL=v;_TYPE=t;_KIND=k} in
 let hj' = apply_pcoercion p hj t2 in
 if the_conv_x_leq isevars env hj'._TYPE c1 then hj'
 else failwith "inh_coerce_to"

let inh_coerce_to isevars env c1 hj =
  inh_coerce_to1 isevars env c1 hj._VAL hj._TYPE hj._KIND

let rec inh_conv_coerce1 isevars env c1 v t k =
 if the_conv_x_leq isevars env t c1 
 then {_VAL=v; _TYPE=t; _KIND=k}
 else try inh_coerce_to1 isevars env c1 v t k
 with _ ->  (* try ... with _ -> ... is BAD *)

   (match (hnf_constr !isevars t,hnf_constr !isevars c1) with
      | (DOP2(Prod,t1,DLAM(_,t2)),DOP2(Prod,u1,DLAM(name,u2))) -> 
          let v' = hnf_constr !isevars v in
            if (match v' with
                    DOP2(Lambda,v1,DLAM(_,v2)) ->
                      the_conv_x isevars env v1 u1 (* leq v1 u1? *)
                  |         _                -> false)
            then 
	      let (x,v1,v2) = destLambda v' in
(*              let jv1 = exemeta_rec def_vty_con isevars env v1 in 
	      let assv1 = assumption_of_judgement !isevars env jv1 in
 *)
	      let assv1 = outcast_type v1 in
              let env1 = add_rel (x,assv1) env in
              let h2 = inh_conv_coerce1 isevars env1 u2 v2 t2 (mkSort (sort_of !isevars env1 t2)) in
              abs_rel !isevars x assv1 h2
            else 
(*
	      let ju1 = exemeta_rec def_vty_con isevars env u1 in 
              let assu1 = assumption_of_judgement !isevars env ju1 in
 *)
	      let assu1 = outcast_type u1 in
              let name = (match name with Anonymous -> Name (id_of_string "x")
                            | _ -> name) in
              let env1 = add_rel (name,assu1) env in
              let h1 = 
		inh_conv_coerce1 isevars env1 t1 (Rel 1) u1 (mkSort (level_of_type assu1)) in
              let h2 = inh_conv_coerce1 isevars env1 u2  
			 (DOPN(AppL,[|(lift 1 v);h1._VAL|])) 
                         (subst1 h1._VAL t2) 
			 (mkSort (sort_of !isevars env1 t2)) in
	      abs_rel !isevars name assu1 h2
      | _ -> failwith "inh_coerce_to")
            
let inh_conv_coerce isevars env c1 hj =
  inh_conv_coerce1 isevars env c1 hj._VAL hj._TYPE hj._KIND

let inh_cast_rel isevars env cj tj =
    let cj' = (try inh_conv_coerce isevars env tj._VAL cj 
              with Not_found | Failure _ -> error_actual_type CCI env 
		  (j_nf_ise !isevars cj) (j_nf_ise !isevars tj)) in
      { _VAL = mkCast cj'._VAL tj._VAL;
        _TYPE = tj._VAL;
        _KIND = whd_betadeltaiota !isevars tj._TYPE}

let inh_apply_rel_list nocheck isevars env argjl funj vtcon =
  let rec apply_rec acc typ = function
    [] -> let resj =
      {_VAL=applist(j_val_only funj,List.map j_val_only (List.rev acc));
       _TYPE= typ;
       _KIND = funj._KIND} in
      (match vtcon with 
      | (_,(_,Some typ')) ->
          (try inh_conv_coerce isevars env typ' resj
          with _ -> resj) (* try ... with _ -> ... is BAD *)
      | (_,(_,None)) -> resj)

  | hj::restjl ->
      match whd_betadeltaiota !isevars typ with
          DOP2(Prod,c1,DLAM(_,c2)) ->
            let hj' =
              if nocheck then hj else 
	      (try inh_conv_coerce isevars env c1 hj 
               with (Failure _ | Not_found) ->
                 error_cant_apply "Type Error" CCI env
		   (j_nf_ise !isevars funj) (jl_nf_ise !isevars argjl)) in
            apply_rec (hj'::acc) (subst1 hj'._VAL c2) restjl
        | _ ->
            error_cant_apply "Non-functional construction" CCI env
	      (j_nf_ise !isevars funj) (jl_nf_ise !isevars argjl)
  in apply_rec [] funj._TYPE argjl
;;
