
(* $Id$ *)

open Util;;
open Generic;;
open Names;;
open Term;;
open Reduction;;
open Environ;;
open Typeops;;
open Type_errors;;
open Classops;;
open Recordops;;
open Evarconv;;

(* Typing operations dealing with coercions *)

let class_of1 env sigma t = class_of sigma (nf_ise1 env sigma t);;

let j_nf_ise env sigma {uj_val=v;uj_type=t;uj_kind=k} =
  {uj_val=nf_ise1 env sigma v;uj_type=nf_ise1 env sigma t;uj_kind=k}
let jl_nf_ise env sigma = List.map (j_nf_ise env sigma)

(* Here, funj is a coercion therefore already typed in global context *)
let apply_coercion_args env argl funj =
  let rec apply_rec acc typ = function
      [] -> {uj_val=applist(j_val_only funj,argl);
             uj_type= typ;
             uj_kind = funj.uj_kind}
    | h::restl ->
 (* On devrait pouvoir s'arranger pour qu'on ait pas à faire hnf_constr *)
  match whd_betadeltaiota env Evd.empty typ with
     DOP2(Prod,c1,DLAM(_,c2)) -> (* Typage garanti par l'appel a app_coercion*)
       apply_rec (h::acc) (subst1 h c2) restl
    | _ -> anomaly "apply_coercion_args"
  in apply_rec [] funj.uj_type argl;;

(* appliquer le chemin de coercions p a` hj *)

let apply_pcoercion env p hj typ_cl =
  if !compter then
    (nbpathc := !nbpathc +1; nbcoer := !nbcoer + (List.length p));
  try fst (List.fold_left
             (fun (ja,typ_cl) i -> 
                let fv,b= coe_value i in
                let argl = (class_args_of typ_cl)@[ja.uj_val] in
                let jres = apply_coercion_args env argl fv in
                  (if b then {uj_type=jres.uj_type;uj_kind=jres.uj_kind;uj_val=ja.uj_val}
                   else jres),jres.uj_type)
             (hj,typ_cl) p)
  with _ -> failwith "apply_pcoercion"

let inh_app_fun env isevars j = 
 match whd_betadeltaiota env !isevars j.uj_type with
    DOP2(Prod,_,DLAM(_,_)) -> j
   | _ ->
       (try
 	let t,i1 = class_of1 env !isevars j.uj_type in
      	let p = lookup_path_to_fun_from i1 in
        apply_pcoercion env p j t
      with _ -> j)
(* find out which exc we must trap (e.g we don't want to catch Sys.Break!) *)

let inh_tosort_force env isevars j =
  let t,i1 = class_of1 env !isevars j.uj_type in
  let p = lookup_path_to_sort_from i1 in
  apply_pcoercion env p j t 

let inh_tosort env isevars j = 
  let typ = whd_betadeltaiota env !isevars j.uj_type in
  match typ with
    DOP0(Sort(_)) -> j  (* idem inh_app_fun *)
  | _ -> (try inh_tosort_force env isevars j with _ -> j)

let inh_ass_of_j env isevars j =
   let typ = whd_betadeltaiota env !isevars j.uj_type in
     match typ with
         DOP0(Sort s) -> {body=j.uj_val;typ=s}
       | _ ->
           (try
             let j1 = inh_tosort_force env isevars j
             in assumption_of_judgment env !isevars j1 
           with _ -> error_assumption CCI env (nf_ise1 env !isevars j.uj_val))
                   (* try ... with _ -> ... is BAD *)

let inh_coerce_to1 env isevars c1 v t k =
 let t1,i1 = class_of1 env !isevars c1 in
 let t2,i2 = class_of1 env !isevars t in
 let p = lookup_path_between (i2,i1) in
 let hj = {uj_val=v;uj_type=t;uj_kind=k} in
 let hj' = apply_pcoercion env p hj t2 in
 if the_conv_x_leq env isevars hj'.uj_type c1 then hj'
 else failwith "inh_coerce_to"

let inh_coerce_to env isevars c1 hj =
  inh_coerce_to1 env isevars c1 hj.uj_val hj.uj_type hj.uj_kind

let rec inh_conv_coerce1 env isevars c1 v t k =
 if the_conv_x_leq env isevars t c1 
 then {uj_val=v; uj_type=t; uj_kind=k}
 else try inh_coerce_to1 env isevars c1 v t k
 with _ ->  (* try ... with _ -> ... is BAD *)

(*   (match (hnf_constr !isevars t,hnf_constr !isevars c1) with*)
   (match (whd_betadeltaiota env !isevars t,
	   whd_betadeltaiota env !isevars c1) with
      | (DOP2(Prod,t1,DLAM(_,t2)),DOP2(Prod,u1,DLAM(name,u2))) -> 
(*          let v' = hnf_constr !isevars v in*)
          let v' = whd_betadeltaiota env !isevars v in
            if (match v' with
                    DOP2(Lambda,v1,DLAM(_,v2)) ->
                      the_conv_x env isevars v1 u1 (* leq v1 u1? *)
                  |         _                -> false)
            then 
	      let (x,v1,v2) = destLambda v' in
(*              let jv1 = exemeta_rec def_vty_con env isevars v1 in 
	      let assv1 = assumption_of_judgement env !isevars jv1 in
 *)
	      let assv1 = outcast_type v1 in
              let env1 = push_rel (x,assv1) env in
              let h2 = inh_conv_coerce1 env1 isevars u2 v2 t2 (mkSort (sort_of env !isevars1 t2)) in
              abs_rel !isevars x assv1 h2
            else 
(*
	      let ju1 = exemeta_rec def_vty_con env isevars u1 in 
              let assu1 = assumption_of_judgement env !isevars ju1 in
 *)
	      let assu1 = outcast_type u1 in
              let name = (match name with Anonymous -> Name (id_of_string "x")
                            | _ -> name) in
              let env1 = add_rel (name,assu1) env in
              let h1 = 
		inh_conv_coerce1 env isevars1 t1 (Rel 1) u1 (mkSort (level_of_type assu1)) in
              let h2 = inh_conv_coerce1 env isevars1 u2  
			 (DOPN(AppL,[|(lift 1 v);h1.uj_val|])) 
                         (subst1 h1.uj_val t2) 
			 (mkSort (sort_of env !isevars1 t2)) in
	      abs_rel !isevars name assu1 h2
      | _ -> failwith "inh_coerce_to")
            
let inh_conv_coerce env isevars c1 hj =
  inh_conv_coerce1 env isevars c1 hj.uj_val hj.uj_type hj.uj_kind

let inh_cast_rel env isevars cj tj =
    let cj' = (try inh_conv_coerce env isevars tj.uj_val cj 
              with Not_found | Failure _ -> error_actual_type CCI env 
		  (j_nf_ise !isevars cj) (j_nf_ise !isevars tj)) in
      { uj_val = mkCast cj'.uj_val tj.uj_val;
        uj_type = tj.uj_val;
        uj_kind = whd_betadeltaiota env !isevars tj.uj_type}

let inh_apply_rel_list nocheck env isevars argjl funj vtcon =
  let rec apply_rec acc typ = function
    [] -> let resj =
      {uj_val=applist(j_val_only funj,List.map j_val_only (List.rev acc));
       uj_type= typ;
       uj_kind = funj.uj_kind} in
      (match vtcon with 
      | (_,(_,Some typ')) ->
          (try inh_conv_coerce env isevars typ' resj
          with _ -> resj) (* try ... with _ -> ... is BAD *)
      | (_,(_,None)) -> resj)

  | hj::restjl ->
      match whd_betadeltaiota env !isevars typ with
          DOP2(Prod,c1,DLAM(_,c2)) ->
            let hj' =
              if nocheck then hj else 
	      (try inh_conv_coerce env isevars c1 hj 
               with (Failure _ | Not_found) ->
                 error_cant_apply "Type Error" CCI env
		   (j_nf_ise !isevars funj) (jl_nf_ise !isevars argjl)) in
            apply_rec (hj'::acc) (subst1 hj'.uj_val c2) restjl
        | _ ->
            error_cant_apply "Non-functional construction" CCI env
	      (j_nf_ise !isevars funj) (jl_nf_ise !isevars argjl)
  in apply_rec [] funj.uj_type argjl
;;
