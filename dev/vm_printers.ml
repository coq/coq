open Format
open Term
open Constr
open Names
open Cemitcodes
open Vmvalues

let ppripos (ri,pos) =
  (match ri with
  | Reloc_annot a ->
      let sp,i = a.ci.ci_ind in
      print_string
        ("annot : MutInd("^(MutInd.to_string sp)^","^(string_of_int i)^")\n")
  | Reloc_const _ ->
      print_string "structured constant\n"
  | Reloc_getglobal kn ->
    print_string ("getglob "^(Constant.to_string kn)^"\n")
  | Reloc_proj_name p ->
    print_string ("proj "^(Projection.Repr.to_string p)^"\n")
  );
   print_flush ()

let print_vfix () = print_string "vfix"
let print_vfix_app () = print_string "vfix_app"
let print_vswith () = print_string "switch"

let ppsort = function
  | Set -> print_string "Set"
  | Prop -> print_string "Prop"
  | Type u -> print_string "Type"



let print_idkey idk =
  match idk with
  | ConstKey sp ->
      print_string "Cons(";
      print_string (Constant.to_string sp);
      print_string ")"
  | VarKey id -> print_string (Id.to_string id)
  | RelKey i -> print_string "~";print_int i
  | EvarKey evk ->
    print_string "Evar(";
    print_int (Evar.repr evk);
    print_string ")"

let rec ppzipper z =
  match z with
  | Zapp args ->
      let n = nargs args in
      open_hbox ();
      for i = 0 to n-2 do
	ppvalues (arg args i);print_string ";";print_space()
      done;
      if n-1 >= 0 then ppvalues (arg args (n-1));
      close_box()
  | Zfix _ -> print_string "Zfix"
  | Zswitch _ -> print_string "Zswitch"
  | Zproj _ -> print_string "Zproj"

and ppstack s =
  open_hovbox 0;
  print_string "[";
  List.iter (fun z -> ppzipper z;print_string " | ") s;
  print_string "]";
  close_box()

and ppatom a =
  match a with
  | Aid idk -> print_idkey idk
  | Asort u -> print_string "Sort(...)"
  | Aind(sp,i) ->  print_string "Ind(";
      print_string (MutInd.to_string sp);
      print_string ","; print_int i;
      print_string ")"

and ppwhd whd =
  match whd with
  | Vprod _ -> print_string "product"
  | Vfun _ -> print_string "function"
  | Vfix _ -> print_vfix()
  | Vcofix _ -> print_string "cofix"
  | Vconstr_const i -> print_string "C(";print_int i;print_string")"
  | Vconstr_block b -> ppvblock b
  | Vatom_stk(a,s) ->
      open_hbox();ppatom a;close_box();
      print_string"@";ppstack s
  | Vuniv_level lvl -> Feedback.msg_notice (Univ.Level.pr lvl)

and ppvblock b =
  open_hbox();
  print_string "Cb(";print_int (btag b);
  let n = bsize b in
  for i = 0 to n -1 do
    print_string ",";ppvalues (bfield b i)
  done;
  print_string")";
  close_box()

and ppvalues v =
  open_hovbox 0;ppwhd (whd_val v);close_box();
  print_flush()
