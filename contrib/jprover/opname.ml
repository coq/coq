open Printf

type token = string
type atom = string list

let opname_token = String.make 4 (Char.chr 0)

type opname =
   { mutable opname_token : token;
     mutable opname_name : string list
   }

let (optable : (string list, opname) Hashtbl.t) = Hashtbl.create 97

(* * Constructors.*)
let nil_opname = { opname_token = opname_token; opname_name = [] }

let _ = Hashtbl.add optable [] nil_opname

let rec mk_opname s ({ opname_token = token; opname_name = name } as opname) =
   if token == opname_token then
      let name = s :: name in
         try Hashtbl.find optable name with
            Not_found ->
               let op = { opname_token = opname_token; opname_name = name } in
                  Hashtbl.add optable name op;
                  op
   else
      mk_opname s (normalize_opname opname)

and make_opname = function
 | [] ->
      nil_opname
 | h :: t ->
      mk_opname h (make_opname t)

and normalize_opname opname =
   if opname.opname_token == opname_token then
      (* This opname is already normalized *)
      opname
   else
      let res = make_opname opname.opname_name
      in
         opname.opname_name <- res.opname_name;
         opname.opname_token <- opname_token;
         res

(*  * Atoms are the inner string list. *)
let intern opname =
   if opname.opname_token == opname_token then
      opname.opname_name
   else
      let name = (normalize_opname opname).opname_name in
         opname.opname_token <- opname_token;
         opname.opname_name <- name;
         name

let eq_inner op1 op2 =
   op1.opname_name <- (normalize_opname op1).opname_name;
   op1.opname_token <- opname_token;
   op2.opname_name <- (normalize_opname op2).opname_name;
   op2.opname_token <- opname_token;
   op1.opname_name == op2.opname_name

let eq op1 op2 =
   (op1.opname_name == op2.opname_name)
   or ((op1.opname_token != opname_token or op2.opname_token != opname_token) & eq_inner op1 op2)

(* * Destructor. *)
let dst_opname = function
 |  { opname_name = n :: name } -> n, { opname_token = opname_token; opname_name = name }
 | _ -> raise (Invalid_argument "dst_opname")

let dest_opname { opname_name = name } =
   name

let string_of_opname op =
   let rec flatten = function
    | [] ->
         ""
    | h::t ->
         let rec collect s = function
          | h::t ->
               collect (h ^ "!" ^ s) t
          | [] ->
               s
         in
            collect h t
   in
      flatten op.opname_name
