open Format
open Term
open Names
open Vmemitcodes
open Values
open Vmvalues

let ppripos (ri,pos) =
  (match ri with
  | Reloc_annot a ->
      print_string "switch\n"
  | Reloc_const _ ->
      print_string "structured constant\n"
  | Reloc_getglobal kn ->
    print_string ("getglob "^(Constant.to_string kn)^"\n")
  | Reloc_caml_prim op ->
    print_string ("caml primitive "^ CPrimitives.to_string @@ Vmbytecodes.caml_prim_to_prim op)
  );
   print_flush ()

let ppsort = function
  | SProp -> print_string "SProp"
  | Set -> print_string "Set"
  | Prop -> print_string "Prop"
  | Type _ -> print_string "Type"
  | QSort _ -> print_string "QSort"

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
  | Vfix _ -> print_string "vfix"
  | Vcofix _ -> print_string "cofix"
  | Vconst i -> print_string "C(";print_int i;print_string")"
  | Vblock b -> ppvblock b
  | Vint64 i -> printf "int64(%LiL)" i
  | Vfloat64 f -> printf "float64(%.17g)" f
  | Vstring s -> printf "string(%S)" (Pstring.to_string s)
  | Varray t -> ppvarray t
  | Vaccu (a, s) ->
      open_hbox();ppatom a;close_box();
      print_string"@";ppstack s

and ppvblock b =
  open_hbox();
  print_string "Cb(";print_int (btag b);
  let n = bsize b in
  for i = 0 to n -1 do
    print_string ",";ppvalues (bfield b i)
  done;
  print_string")";
  close_box()

and ppvarray t =
  let length = Parray.length_int t in
  open_hbox();
  print_string "[|";
  for i = 0 to length - 2 do
    ppvalues (Parray.get t (Uint63.of_int i));
    print_string "; "
  done;
  ppvalues (Parray.get t (Uint63.of_int (length - 1)));
  print_string " | ";
  ppvalues (Parray.default t);
  print_string " |]";
  close_box()

and ppvalues v =
  open_hovbox 0;ppwhd (whd_val v);close_box();
  print_flush()
