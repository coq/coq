open Names
open Term

type tag = int 

type structured_constant =
  | Const_sorts of sorts
  | Const_ind of inductive
  | Const_b0 of tag                
  | Const_bn of tag * structured_constant array

type reloc_table = (tag * int) array 

type annot_switch = 
   {ci : case_info; rtbl : reloc_table; tailcall : bool}
 
module Label = 
  struct
    type t = int
    let no = -1
    let counter = ref no
    let create () = incr counter; !counter
    let reset_label_counter () = counter := no 
  end


type instruction =
  | Klabel of Label.t
  | Kacc of int
  | Kenvacc of int
  | Koffsetclosure of int
  | Kpush
  | Kpop of int
  | Kpush_retaddr of Label.t
  | Kapply of int                       (*  number of arguments *)
  | Kappterm of int * int               (* number of arguments, slot size *)
  | Kreturn of int                      (* slot size *)
  | Kjump
  | Krestart
  | Kgrab of int                        (* number of arguments *)
  | Kgrabrec of int                     (* rec arg *)
  | Kcograb of int                      (* number of arguments *)
  | Kclosure of Label.t * int           (* label, number of free variables *)
  | Kclosurerec of int * int * Label.t array * Label.t array 
                   (* nb fv, init, lbl types, lbl bodies *)
  | Kgetglobal of constant
  | Kconst of structured_constant
  | Kmakeblock of int * tag             (* size, tag *)
  | Kmakeprod 
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kforce
  | Kswitch of Label.t array * Label.t array (* consts,blocks *)
  | Kpushfield of int 
  | Kstop
  | Ksequence of bytecodes * bytecodes

and bytecodes = instruction list

type fv_elem = FVnamed of identifier | FVrel of int

type fv = fv_elem array


(* --- Pretty print *)
open Format
let rec instruction ppf = function
  | Klabel lbl -> fprintf ppf "L%i:" lbl
  | Kacc n -> fprintf ppf "\tacc %i" n
  | Kenvacc n -> fprintf ppf "\tenvacc %i" n
  | Koffsetclosure n -> fprintf ppf "\toffsetclosure %i" n
  | Kpush -> fprintf ppf "\tpush"
  | Kpop n -> fprintf ppf "\tpop %i" n
  | Kpush_retaddr lbl -> fprintf ppf "\tpush_retaddr L%i" lbl
  | Kapply n -> fprintf ppf "\tapply %i" n
  | Kappterm(n, m) ->
      fprintf ppf "\tappterm %i, %i" n m
  | Kreturn n -> fprintf ppf "\treturn %i" n
  | Kjump -> fprintf ppf "\tjump"
  | Krestart -> fprintf ppf "\trestart"
  | Kgrab n -> fprintf ppf "\tgrab %i" n
  | Kgrabrec n -> fprintf ppf "\tgrabrec %i" n
  | Kcograb n -> fprintf ppf "\tcograb %i" n
  | Kclosure(lbl, n) ->
      fprintf ppf "\tclosure L%i, %i" lbl n
  | Kclosurerec(fv,init,lblt,lblb) ->
      fprintf ppf "\tclosurerec";
      fprintf ppf "%i , %i, " fv init;
      print_string "types = ";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblt;
      print_string " bodies = ";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblb;
                   (* nb fv, init, lbl types, lbl bodies *)
  | Kgetglobal id -> fprintf ppf "\tgetglobal %s" (Names.string_of_con id)
  | Kconst cst ->
      fprintf ppf "\tconst"
  | Kmakeblock(n, m) ->
      fprintf ppf "\tmakeblock %i, %i" n m
  | Kmakeprod -> fprintf ppf "\tmakeprod"
  | Kmakeswitchblock(lblt,lbls,_,sz) ->
      fprintf ppf "\tmakeswitchblock %i, %i, %i" lblt lbls sz
  | Kforce -> fprintf ppf "\tforce"
  | Kswitch(lblc,lblb) -> 
      fprintf ppf "\tswitch";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblc;
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblb;
  | Kpushfield n -> 
      fprintf ppf "\tpushfield %i" n
  | Kstop -> fprintf ppf "\tstop"
  | Ksequence (c1,c2) ->
      fprintf ppf "%a@ %a" instruction_list c1 instruction_list c2 

and instruction_list ppf = function
    [] -> ()
  | Klabel lbl :: il ->
      fprintf ppf "L%i:%a" lbl instruction_list il
  | instr :: il ->
      fprintf ppf "%a@ %a" instruction instr instruction_list il
 
let draw_instr c =
  fprintf std_formatter "@[<v 0>%a@]" instruction_list c
