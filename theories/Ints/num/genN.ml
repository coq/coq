open Format

let size = 13
let sizeaux = 1

let t = "t"
let c = "N"
let gen_proof = false
let gen_proof1 = (* true *) false
let gen_proof2 = (* true *) false
let gen_proof3 = false
let gen_proof4 = (* true *) false
let gen_proof5 = false
let gen_proof6 = (* true *) false
let gen_proof7 = false
let gen_proof8 = false
let gen_proof9 = false
let gen_proof10 = (* true *) false
let gen_proof11 = false
let gen_proof12 = false
let gen_proof13 = false
let gen_proof14 = (* true *) false


(******* Start Printing ********)
let basename = "N"


let print_header fmt l =
  let l = "ZArith"::"Basic_type"::"ZnZ"::"Zn2Z"::"Nbasic"::"GenMul"::
	  "GenDivn1"::"Wf_nat"::l in
  List.iter (fun s -> fprintf fmt "Require Import %s.\n" s) l;
  fprintf fmt "\n"

let start_file post l =
  let outname = basename^post^".v" in
  let fd = 
    try 
      Unix.openfile outname [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC] 0o640 
    with _ -> 
      print_string ("can not open file "^outname^"\n"); 
      exit 1  in
  let out = Unix.out_channel_of_descr fd in
  set_binary_mode_out out false;
  let fmt = formatter_of_out_channel out in
  print_header fmt l;
  fmt

 

(****** Print types *******)

let print_Make () =
  let fmt = start_file "Make" [] in

  fprintf fmt "Module Type W0Type.\n";
  fprintf fmt " Parameter w : Set.\n";
  fprintf fmt " Parameter w_op : znz_op w.\n";
  fprintf fmt " Parameter w_spec : znz_spec w_op.\n";
  fprintf fmt "End W0Type.\n";
  fprintf fmt "\n";

  fprintf fmt "Module Make (W0:W0Type).\n";
  fprintf fmt " Import W0.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition w0 := W0.w.\n";
  for i = 1 to size do
    fprintf fmt " Definition w%i := zn2z w%i.\n" i (i-1)
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition w0_op := W0.w_op.\n";
  for i = 1 to 3 do
    fprintf fmt " Definition w%i_op := mk_zn2z_op w%i_op.\n" i (i-1)
  done;
  for i = 4 to size + 3 do
    fprintf fmt " Definition w%i_op := mk_zn2z_op_karatsuba w%i_op.\n" i (i-1)
  done;
  fprintf fmt "\n";

  fprintf fmt " Section Make_op.\n";
  fprintf fmt "  Variable mk : forall w', znz_op w' -> znz_op (zn2z w').\n";
  fprintf fmt "\n";
  fprintf fmt 
    "  Fixpoint make_op_aux (n:nat) : znz_op (word w%i (S n)):=\n" size;
  fprintf fmt "   match n return znz_op (word w%i (S n)) with\n" size;
  fprintf fmt "   | O => w%i_op\n" (size+1);
  fprintf fmt "   | S n1 =>\n";
  fprintf fmt "     match n1 return znz_op (word w%i (S (S n1))) with\n" size;
  fprintf fmt "     | O => w%i_op\n" (size+2);
  fprintf fmt "     | S n2 =>\n";
  fprintf fmt "       match n2 return znz_op (word w%i (S (S (S n2)))) with\n"
    size;
  fprintf fmt "       | O => w%i_op\n" (size+3);
  fprintf fmt "       | S n3 => mk _ (mk _ (mk _ (make_op_aux n3)))\n";
  fprintf fmt "       end\n";
  fprintf fmt "     end\n";
  fprintf fmt "   end.\n";
  fprintf fmt "\n";
  fprintf fmt " End Make_op.\n";
  fprintf fmt "\n";
  fprintf fmt " Definition make_op := make_op_aux mk_zn2z_op_karatsuba.\n";
  fprintf fmt "\n";

  fprintf fmt " Inductive %s_ : Set :=\n" t;
  for i = 0 to size do 
    fprintf fmt "  | %s%i : w%i -> %s_\n" c i i t
  done;
  fprintf fmt "  | %sn : forall n, word w%i (S n) -> %s_.\n" c size t;
  fprintf fmt "\n";
  fprintf fmt " Definition %s := %s_.\n" t t;
  fprintf fmt "\n";
  
  fprintf fmt " Definition w_0 := w0_op.(znz_0).\n";
  fprintf fmt "\n";

  for i = 0 to size do
    fprintf fmt " Definition one%i := w%i_op.(znz_1).\n" i i
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition zero := %s0 w_0.\n" c;
  fprintf fmt " Definition one := %s0 one0.\n" c;
  fprintf fmt "\n";

  (* Successor function *)    
  for i = 0 to size do
    fprintf fmt " Definition w%i_succ_c := w%i_op.(znz_succ_c).\n" i i
  done;
  fprintf fmt "\n";

  for i = 0 to size do
    fprintf fmt " Definition w%i_succ := w%i_op.(znz_succ).\n" i i
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition succ x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size-1 do
    fprintf fmt "  | %s%i wx =>\n" c i;
    fprintf fmt "    match w%i_succ_c wx with\n" i;
    fprintf fmt "    | C0 r => %s%i r\n" c i; 
    fprintf fmt "    | C1 r => %s%i (WW one%i r)\n" c (i+1) i;
    fprintf fmt "    end\n";
  done;
  fprintf fmt "  | %s%i wx =>\n" c size;
  fprintf fmt "    match w%i_succ_c wx with\n" size;
  fprintf fmt "    | C0 r => %s%i r\n" c size; 
  fprintf fmt "    | C1 r => %sn 0 (WW one%i r)\n" c size ;
  fprintf fmt "    end\n";
  fprintf fmt "  | %sn n wx =>\n" c;
  fprintf fmt "    let op := make_op n in\n";
  fprintf fmt "    match op.(znz_succ_c) wx with\n";
  fprintf fmt "    | C0 r => %sn n r\n" c; 
  fprintf fmt "    | C1 r => %sn (S n) (WW op.(znz_1) r)\n" c;
  fprintf fmt "    end\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  for i = 1 to size do 
    fprintf fmt " Definition extend%i :=\n" i;
    fprintf fmt "  Eval lazy beta zeta iota delta [extend]in extend %i.\n" i
  done;
  fprintf fmt "\n";
  
  for i = 0 to size do
    fprintf fmt " Definition w%i_eq0 := w%i_op.(znz_eq0).\n" i i
  done;
  fprintf fmt "\n";
 
  for i = 0 to size do
    fprintf fmt " Definition w%i_0W := w%i_op.(znz_0W).\n" i i
  done;
  fprintf fmt "\n";
  fprintf fmt " Definition w0_WW := w0_op.(znz_WW).\n";
  fprintf fmt "\n";

  (* Addition *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_add_c := w%i_op.(znz_add_c).\n" i i 
  done;
  fprintf fmt "\n";
(*
  fprintf fmt " Definition add_c_1_0 x y :=\n";
  fprintf fmt "  match x with\n";
  fprintf fmt "  | W0 => C0 (w0_0W y)\n";
  fprintf fmt "  | WW xh xl => 
  fprintf fmt "    match w1_add_c xl y with\n";
  fprintf fmt "    | C0 rl => C0 (WW xh rl)\n";
  fprintf fmt "    | C1 rl =>\n";
  fprintf fmt "      match  w1_succ_c xh with\n";
  fprintf fmt "      | C0 rh => C0 (WW rh rl)\n";
  fprintf fmt "      | C1 rh => C1 (w0_WW rh rl)\n";
  fprintf fmt "      end\n";
  fprintf fmt "    end\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  for i = 1 to size do
    fprintf fmt " Definition add_c_n_%i :=\n" i;
    fprintf fmt "  add_c_smn1 w%i
*)                  
             
  for i = 0 to size do 
    fprintf fmt " Definition w%i_add x y :=\n" i;
    fprintf fmt "  match w%i_add_c x y with\n" i;
    fprintf fmt "  | C0 r => %s%i r\n" c i;
    fprintf fmt "  | C1 r => ";
    if i < size then fprintf fmt "%s%i (WW one%i r)\n" c (i+1) i
    else fprintf fmt "%sn 0 (WW one%i r)\n" c size;
    fprintf fmt "  end.\n"
  done;
  fprintf fmt " Definition addn n (x y : word w%i (S n)) :=\n" size;
  fprintf fmt "  let op := make_op n in\n";
  fprintf fmt "  match op.(znz_add_c) x y with\n";
  fprintf fmt "  | C0 r => %sn n r\n" c;
  fprintf fmt "  | C1 r => %sn (S n) (WW op.(znz_1) r)" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition add x y :=\n";
  fprintf fmt "  match x, y with\n";
  fprintf fmt "  | %s0 wx, %s0 wy => w0_add wx wy \n" c c;
  for j = 1 to size do 
    fprintf fmt "  | %s0 wx, %s%i wy =>\n" c c j;
    fprintf fmt "    if w0_eq0 wx then y else w%i_add " j;
    if j = 1 then fprintf fmt "(WW w_0 wx) wy\n"
    else fprintf fmt "(extend%i w0 (WW w_0 wx)) wy\n" (j-1)
  done;
  fprintf fmt "  | %s0 wx, %sn n wy =>\n" c c; 
  fprintf fmt "    if w0_eq0 wx then y\n";
  fprintf fmt "    else addn n (extend n w%i (extend%i w0 (WW w_0 wx))) wy\n"
    size size;
  for i = 1 to size do
    fprintf fmt "  | %s%i wx, %s0 wy =>\n" c i c;
    fprintf fmt 
     "    if w0_eq0 wy then x else w%i_add wx " i;
    if i = 1 then fprintf fmt "(WW w_0 wy)\n"
    else fprintf fmt "(extend%i w0 (WW w_0 wy))\n" (i-1);
    for j = 1 to size do
      fprintf fmt "  | %s%i wx, %s%i wy => " c i c j;
      if i < j then fprintf fmt "w%i_add (extend%i w%i wx) wy\n" j (j-i) (i-1)
      else if i = j then  fprintf fmt "w%i_add wx wy\n" j 
      else fprintf fmt "w%i_add wx (extend%i w%i wy)\n" i (i-j) (j-1)
    done;
    fprintf fmt   
      "  | %s%i wx, %sn n wy => addn n (extend n w%i (extend%i w%i wx)) wy\n" 
      c i c size (size-i+1) (i-1)
  done;
  fprintf fmt "  | %sn n wx, %s0 wy =>\n" c c; 
  fprintf fmt "    if w0_eq0 wy then x\n";
  fprintf fmt "    else addn n wx (extend n w%i (extend%i w0 (WW w_0 wy)))\n" 
    size size;
  for j = 1 to size do
    fprintf fmt 
      "  | %sn n wx, %s%i wy => addn n wx (extend n w%i (extend%i w%i wy))\n"
       c c j size (size-j+1) (j-1); 
  done; 
  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "     addn mn\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d)))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition reduce_0 (x:w) := %s0 x.\n" c; 
  fprintf fmt " Definition reduce_1 :=\n";
  fprintf fmt "  Eval lazy beta iota delta[reduce_n1] in\n";
  fprintf fmt "   reduce_n1 _ _ zero w0_eq0 %s0 %s1.\n" c c;
  for i = 2 to size do
    fprintf fmt " Definition reduce_%i :=\n" i;
    fprintf fmt "  Eval lazy beta iota delta[reduce_n1] in\n";
    fprintf fmt "   reduce_n1 _ _ zero w%i_eq0 reduce_%i %s%i.\n" 
      (i-1) (i-1)  c i
  done;
  fprintf fmt " Definition reduce_%i :=\n" (size+1);
  fprintf fmt "  Eval lazy beta iota delta[reduce_n1] in\n";
  fprintf fmt "   reduce_n1 _ _ zero w%i_eq0 reduce_%i (%sn 0).\n" 
    size size c; 
  
  fprintf fmt " Definition reduce_n n := \n";
  fprintf fmt "  Eval lazy beta iota delta[reduce_n] in\n";
  fprintf fmt "   reduce_n _ _ zero reduce_%i %sn n.\n" (size + 1) c;
  fprintf fmt "\n";

  (* Predecessor *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_pred_c := w%i_op.(znz_pred_c).\n" i i
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition pred x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx =>\n" c i;
    fprintf fmt "    match w%i_pred_c wx with\n" i;
    fprintf fmt "    | C0 r => reduce_%i r\n" i; 
    fprintf fmt "    | C1 r => zero\n";
    fprintf fmt "    end\n";
  done;
  fprintf fmt "  | %sn n wx =>\n" c;
  fprintf fmt "    let op := make_op n in\n";
  fprintf fmt "    match op.(znz_pred_c) wx with\n";
  fprintf fmt "    | C0 r => reduce_n n r\n"; 
  fprintf fmt "    | C1 r => zero\n";
  fprintf fmt "    end\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  (* Substraction *)
  fprintf fmt "\n";
  for i = 0 to size do
    fprintf fmt " Definition w%i_sub_c := w%i_op.(znz_sub_c).\n" i i
  done;
  fprintf fmt "\n";

  for i = 0 to size do 
    fprintf fmt " Definition w%i_sub x y :=\n" i;
    fprintf fmt "  match w%i_sub_c x y with\n" i;
    fprintf fmt "  | C0 r => reduce_%i r\n" i;
    fprintf fmt "  | C1 r => zero\n";
    fprintf fmt "  end.\n"
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition subn n (x y : word w%i (S n)) :=\n" size;
  fprintf fmt "  let op := make_op n in\n";
  fprintf fmt "  match op.(znz_sub_c) x y with\n";
  fprintf fmt "  | C0 r => %sn n r\n" c;
  fprintf fmt "  | C1 r => N0 w_0";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition sub x y :=\n";
  fprintf fmt "  match x, y with\n";
  fprintf fmt "  | %s0 wx, %s0 wy => w0_sub wx wy \n" c c;
  for j = 1 to size do 
    fprintf fmt "  | %s0 wx, %s%i wy =>\n" c c j;
    fprintf fmt "    if w0_eq0 wx then zero else w%i_sub " j;
    if j = 1 then fprintf fmt "(WW w_0 wx) wy\n"
    else fprintf fmt "(extend%i w0 (WW w_0 wx)) wy\n" (j-1)
  done;
  fprintf fmt "  | %s0 wx, %sn n wy =>\n" c c; 
  fprintf fmt "    if w0_eq0 wx then zero\n";
  fprintf fmt "    else subn n (extend n w%i (extend%i w0 (WW w_0 wx))) wy\n"
    size size;
  for i = 1 to size do
    fprintf fmt "  | %s%i wx, %s0 wy =>" c i c;
    fprintf fmt  "\n    if w0_eq0 wy then x\n";
    fprintf fmt "    else w%i_sub wx " i;
    if i = 1 then fprintf fmt "(WW w_0 wy)\n"
    else fprintf fmt "(extend%i w0 (WW w_0 wy))\n" (i-1);
    for j = 1 to size do
      fprintf fmt "  | %s%i wx, %s%i wy => " c i c j;
      if i < j then fprintf fmt "w%i_sub (extend%i w%i wx) wy\n" j (j-i) (i-1)
      else if i = j then  fprintf fmt "w%i_sub wx wy\n" j 
      else fprintf fmt "w%i_sub wx (extend%i w%i wy)\n" i (i-j) (j-1)
    done;
    fprintf fmt   
      "  | %s%i wx, %sn n wy => subn n (extend n w%i (extend%i w%i wx)) wy\n" 
      c i c size (size-i+1) (i-1)
  done;
  fprintf fmt "  | %sn n wx, %s0 wy =>\n" c c; 
  fprintf fmt "    if w0_eq0 wy then x\n";
  fprintf fmt "    else subn n wx (extend n w%i (extend%i w0 (WW w_0 wy)))\n" 
    size size;
  for j = 1 to size do
    fprintf fmt 
      "  | %sn n wx, %s%i wy => subn n wx (extend n w%i (extend%i w%i wy))\n"
       c c j size (size-j+1) (j-1); 
  done; 
  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "     subn mn\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d)))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n"; 

  for i = 0 to size do
    fprintf fmt " Definition compare_%i := w%i_op.(znz_compare).\n" i i;
    fprintf fmt " Definition comparen_%i :=\n" i;
    let s0 = if i = 0 then "w_0" else "W0" in
    fprintf fmt 
      "  compare_mn_1 w%i w%i %s compare_%i (compare_%i %s) compare_%i.\n" 
                        i   i  s0         i           i  s0          i
  done;
  fprintf fmt "\n"; 

  (* Comparison *)
  fprintf fmt " Definition compare x y :=\n";
  fprintf fmt "  match x, y with\n";
  for i = 0 to size do
    for j = 0 to size do
      fprintf fmt "  | %s%i wx, %s%i wy => " c i c j;
      if i < j then fprintf fmt "opp_compare (comparen_%i %i wy wx)\n" i (j-i)
      else if i = j then fprintf fmt "compare_%i wx wy\n" i
      else fprintf fmt "comparen_%i %i wx wy\n" j (i-j)
    done;
    let s0 = if i = 0 then "w_0" else "W0" in
    fprintf fmt "  | %s%i wx, %sn n wy =>\n" c i c;
    fprintf fmt "    opp_compare (compare_mn_1 w%i w%i %s " size i s0;
    fprintf fmt "compare_%i (compare_%i W0) (comparen_%i %i) (S n) wy wx)\n" 
      i size i (size - i)
  done;
  for j = 0 to size do
    let s0 = if j = 0 then "w_0" else "W0" in
    fprintf fmt "  | %sn n wx, %s%i wy =>\n" c c j;
    fprintf fmt "    compare_mn_1 w%i w%i %s " size j s0;
    fprintf fmt "compare_%i (compare_%i W0) (comparen_%i %i) (S n) wx wy\n" 
      j size j (size - j)
  done;
  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "     op.(znz_compare)\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d)))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition eq_bool x y :=\n";
  fprintf fmt "  match compare x y with\n";
  fprintf fmt "  | Eq => true\n";
  fprintf fmt "  | _  => false\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
  
 
  (* Multiplication *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_mul_c := w%i_op.(znz_mul_c).\n" i i
  done;
  fprintf fmt "\n";
  
  for i = 0 to size do
    let s0 = if i = 0 then "w_0" else "W0" in
    fprintf fmt " Definition w%i_mul_add :=\n" i;
    fprintf fmt "   Eval lazy beta delta [w_mul_add] in\n";
    fprintf fmt "     %sw_mul_add w%i %s w%i_succ w%i_add_c w%i_mul_c.\n" 
      "@" i s0 i i i
  done;
  fprintf fmt "\n";
  
  for i = 0 to size do
    let s0 = if i = 0 then "w_0" else "W0" in
    fprintf fmt " Definition w%i_mul_add_n1 :=\n" i;
    fprintf fmt 
     "  %sgen_mul_add_n1 w%i %s w%i_op.(znz_WW) w%i_0W w%i_mul_add.\n"
        "@"                i s0   i               i               i
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition mul x y :=\n";
  fprintf fmt "  match x, y with\n";
  fprintf fmt "  | %s0 wx, %s0 wy =>\n" c c;
  fprintf fmt "    reduce_1 (w0_mul_c wx wy)\n";
  for j = 1 to size do
    fprintf fmt "  | %s0 wx, %s%i wy =>\n" c c j;
    fprintf fmt "    if w0_eq0 wx then zero\n";
    fprintf fmt "    else\n";
    fprintf fmt "      let (w,r) := w0_mul_add_n1 %i wy wx w_0 in\n" j;
    fprintf fmt "      if w0_eq0 w then %s%i r\n" c j;
    if j = 1 then 
      fprintf fmt "      else %s2 (WW (WW w_0 w) r)\n" c
    else if j = size then 
      fprintf fmt "      else %sn 0 (WW (extend%i w0 (WW w_0 w)) r)\n" 
	c (size-1)
    else
      fprintf fmt "      else %s%i (WW (extend%i w0 (WW w_0 w)) r)\n" 
	c (j+1) (j-1)
  done;

  fprintf fmt "  | %s0 wx, %sn n wy =>\n" c c;
  fprintf fmt "    if w0_eq0 wx then zero\n";
  fprintf fmt "    else\n";
  fprintf fmt "    let (w,r) := w%i_mul_add_n1 (S n) wy " size; 
  fprintf fmt "(extend%i w0 (WW w_0 wx)) W0 in\n" (size - 1);
  fprintf fmt "    if w%i_eq0 w then %sn n r\n" size c;
  fprintf fmt "    else %sn (S n) (WW (extend n w%i (WW W0 w)) r)\n" c size;
  
  for i = 1 to size do
    fprintf fmt "  | %s%i wx, %s0 wy =>\n" c i c;
    fprintf fmt "    if w0_eq0 wy then zero\n";
    fprintf fmt "    else\n";
    fprintf fmt "      let (w,r) := w0_mul_add_n1 %i wx wy w_0 in\n" i;
    fprintf fmt "      if w0_eq0 w then %s%i r\n" c i;
    if i = 1 then 
      fprintf fmt "      else %s2 (WW (WW w_0 w) r)\n" c
    else if i = size then 
      fprintf fmt "      else %sn 0 (WW (extend%i w0 (WW w_0 w)) r)\n" 
	c (size-1)
    else
      fprintf fmt "      else %s%i (WW (extend%i w0 (WW w_0 w)) r)\n" 
	c (i+1) (i-1);
    for j = 1 to size do
      fprintf fmt "  | %s%i wx, %s%i wy =>\n" c i c j;
      if i = j then begin
	if i = size then fprintf fmt "    %sn 0 (w%i_mul_c wx wy)\n" c i
	else fprintf fmt "    %s%i (w%i_mul_c wx wy)\n" c (i+1) i
      end else begin
	let min,max, wmin, wmax = 
	  if i < j then i, j, "wx", "wy" else j, i, "wy", "wx" in
	fprintf fmt "    let (w,r) := w%i_mul_add_n1 %i %s %s W0 in\n" 
	           min (max-min) wmax wmin;
	fprintf fmt "    if w%i_eq0 w then %s%i r\n" min c max;
	fprintf fmt "    else ";
	if max = size then fprintf fmt "%sn 0 " c
	else fprintf fmt "%s%i " c (max+1);
	fprintf fmt "(WW (extend%i w%i w) r)\n" (max - min) (min-1);
      end
    done;
    fprintf fmt "  | %s%i wx, %sn n wy =>\n" c i c;
    fprintf fmt "    let (w,r) := w%i_mul_add_n1 (S n) wy " size; 
    if i = size then fprintf fmt "wx W0 in\n"
    else
      fprintf fmt "(extend%i w%i wx) W0 in\n" (size - i) (i-1);
    fprintf fmt "    if w%i_eq0 w then %sn n r\n" size c;
    fprintf fmt "    else %sn (S n) (WW (extend n w%i (WW W0 w)) r)\n" c size
    
  done;
  fprintf fmt "  | %sn n wx, %s0 wy =>\n" c c;
  fprintf fmt "    if w0_eq0 wy then zero\n";
  fprintf fmt "    else\n";
  fprintf fmt "    let (w,r) := w%i_mul_add_n1 (S n) wx " size; 
  fprintf fmt "(extend%i w0 (WW w_0 wy)) W0 in\n" (size - 1);
  fprintf fmt "    if w%i_eq0 w then %sn n r\n" size c;
  fprintf fmt "    else %sn (S n) (WW (extend n w%i (WW W0 w)) r)\n" c size;
  
  for j = 1 to size do
    fprintf fmt "  | %sn n wx, %s%i wy =>\n" c c j;
    fprintf fmt "    let (w,r) := w%i_mul_add_n1 (S n) wx " size; 
    if j = size then fprintf fmt "wy W0 in\n"
    else
      fprintf fmt "(extend%i w%i wy) W0 in\n" (size - j) (j-1);
    fprintf fmt "    if w%i_eq0 w then %sn n r\n" size c;
    fprintf fmt "    else %sn (S n) (WW (extend n w%i (WW W0 w)) r)\n" c size
  done;

  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "     reduce_n (S mn) (op.(znz_mul_c)\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d))))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
  
  (* Square *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_square_c := w%i_op.(znz_square_c).\n" i i
  done;
  fprintf fmt "\n";
  
  fprintf fmt " Definition square x :=\n";
  fprintf fmt "  match x with\n";
    fprintf fmt "  | %s0 wx => reduce_1 (w0_square_c wx)\n" c;
  for i = 1 to size - 1 do
    fprintf fmt "  | %s%i wx => %s%i (w%i_square_c wx)\n" c i c (i+1) i
  done;
  fprintf fmt "  | %s%i wx => %sn 0 (w%i_square_c wx)\n" c size c size;
  fprintf fmt "  | %sn n wx =>\n" c;
  fprintf fmt "    let op := make_op n in\n";
  fprintf fmt "    %sn (S n) (op.(znz_square_c) wx)\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Fixpoint power_pos (x:%s) (p:positive) {struct p} : %s :=\n"
    t t;
  fprintf fmt "  match p with\n";
  fprintf fmt "  | xH => x\n";
  fprintf fmt "  | xO p => square (power_pos x p)\n";
  fprintf fmt "  | xI p => mul (square (power_pos x p)) x\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
    
  (* Square root *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_sqrt := w%i_op.(znz_sqrt).\n" i i
  done;
  fprintf fmt "\n";
  
  fprintf fmt " Definition sqrt x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx => reduce_%i (w%i_sqrt wx)\n" c i i i;
  done;
  fprintf fmt "  | %sn n wx =>\n" c;
  fprintf fmt "    let op := make_op n in\n";
  fprintf fmt "    reduce_n n (op.(znz_sqrt) wx)\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

    
  (* Division *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_div_gt := w%i_op.(znz_div_gt).\n" i i
  done;
  fprintf fmt "\n";
  
  for i = 0 to size do
    fprintf fmt " Definition w%i_divn1 :=\n"  i;
    fprintf fmt "  gen_divn1 w%i_op.(znz_zdigits) w%i_op.(znz_0)\n" i i;
    fprintf fmt "    w%i_op.(znz_WW) w%i_op.(znz_head0)\n" i i;
    fprintf fmt "    w%i_op.(znz_add_mul_div) w%i_op.(znz_div21)\n" i i;
    fprintf fmt "    w%i_op.(znz_compare) w%i_op.(znz_sub).\n" i i;
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition div_gt x y :=\n";
  fprintf fmt "  match x, y with\n";
  for i = 0 to size do
    for j = 0 to size do
      fprintf fmt "  | %s%i wx, %s%i wy =>" c i c j;
      if i = j then 
	fprintf fmt 
	  " let (q, r):= w%i_div_gt wx wy in (reduce_%i q, reduce_%i r)\n" 
	  i i i
      else if i > j then
	fprintf fmt 
	  " let (q, r):= w%i_divn1 %i wx wy in (reduce_%i q, reduce_%i r)\n"
	  j (i-j) i j
      else begin (* i < j *)
	fprintf fmt 
	  "\n    let wx':= GenBase.extend w%i_0W %i wx in\n" 
	  i (j-i-1);
	fprintf fmt "    let (q, r):= w%i_div_gt wx' wy in\n" j; 
	fprintf fmt "    (reduce_%i q, reduce_%i r)\n" j j;
      end
    done;
    fprintf fmt "  | %s%i wx, %sn n wy =>\n" c i c;
    fprintf fmt
      "    let wx':= extend n w%i (GenBase.extend w%i_0W %i wx) in\n"
	  size i (size-i);
    fprintf fmt "    let (q, r):= (make_op n).(znz_div_gt) wx' wy in\n"; 
    fprintf fmt "    (reduce_n n q, reduce_n n r)\n";
  done;
  for j = 0 to size do
    fprintf fmt "  | %sn n wx, %s%i wy =>\n" c c j;
    if j < size then
      fprintf fmt "    let wy':= GenBase.extend w%i_0W %i wy in\n"
	j (size-j-1)
    else 
      fprintf fmt "    let wy':= wy in\n";
    fprintf fmt "    let (q, r):= w%i_divn1 (S n) wx wy' in\n" size;
    fprintf fmt "    (reduce_n n q, reduce_%i r)\n" size
  done;
  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "    let (q, r):= op.(znz_div)\n";
  fprintf fmt "         (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "         (castm (diff_l n m) (extend_tr wy (fst d))) in\n";
  fprintf fmt "    (reduce_n mn q, reduce_n mn r)\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition div_eucl x y :=\n";
  fprintf fmt "  match compare x y with\n";
  fprintf fmt "  | Eq => (one, zero)\n";
  fprintf fmt "  | Lt => (zero, x)\n";
  fprintf fmt "  | Gt => div_gt x y\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition div x y := fst (div_eucl x y).\n";
  fprintf fmt "\n";
    
  (* Modulo *)  
  for i = 0 to size do
    fprintf fmt " Definition w%i_mod_gt := w%i_op.(znz_mod_gt).\n" i i
  done;
  fprintf fmt "\n";
  
  for i = 0 to size do
    fprintf fmt " Definition w%i_modn1 :=\n"  i;
    fprintf fmt "  gen_modn1 w%i_op.(znz_zdigits) w%i_op.(znz_0)\n" i i;
    fprintf fmt 
      "    w%i_op.(znz_head0) w%i_op.(znz_add_mul_div) w%i_op.(znz_div21)\n"
      i i i;
    fprintf fmt 
      "    w%i_op.(znz_compare) w%i_op.(znz_sub).\n"
      i i;
  done;
  fprintf fmt "\n";

  fprintf fmt " Definition mod_gt x y :=\n";
  fprintf fmt "  match x, y with\n";
  for i = 0 to size do
    for j = 0 to size do
      fprintf fmt "  | %s%i wx, %s%i wy =>"
	c i c j;
      if i = j then 
	fprintf fmt " reduce_%i (w%i_mod_gt wx wy)\n" i i
      else if i > j then
	fprintf fmt 
	  " reduce_%i (w%i_modn1 %i wx wy)\n" j j (i-j)
      else begin (* i < j *)
        fprintf fmt 
	  "\n    let wx':= GenBase.extend w%i_0W %i wx in\n"
	  i (j-i-1);
	fprintf fmt "    reduce_%i (w%i_mod_gt wx' wy)\n" j j; 
      end
    done;
    fprintf fmt "  | %s%i wx, %sn n wy =>\n" c i c;
    fprintf fmt 
      "    let wx':= extend n w%i (GenBase.extend w%i_0W %i wx) in\n"
      size i (size-i);
    fprintf fmt "    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)\n"; 
  done;
  for j = 0 to size do
    fprintf fmt "  | %sn n wx, %s%i wy =>\n" c c j;
    if j < size then
      fprintf fmt "    let wy':= GenBase.extend w%i_0W %i wy in\n"
	j (size-j-1)
    else 
      fprintf fmt "    let wy':= wy in\n";
    fprintf fmt "    reduce_%i (w%i_modn1 (S n) wx wy')\n" size size;
  done;
  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "     reduce_n mn (op.(znz_mod_gt)\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d))))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
  
  fprintf fmt " Definition modulo x y := \n";
  fprintf fmt "  match compare x y with\n";
  fprintf fmt "  | Eq => zero\n";
  fprintf fmt "  | Lt => x\n";
  fprintf fmt "  | Gt => mod_gt x y\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  (* Definition du gcd *)
  fprintf fmt " Definition digits x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do 
    fprintf fmt "  | %s%i _ => w%i_op.(znz_digits)\n" c i i;
  done;
  fprintf fmt "  | %sn n _ => (make_op n).(znz_digits)\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition gcd_gt_body a b cont :=\n";
  fprintf fmt "  match compare b zero with\n";
  fprintf fmt "  | Gt =>\n";  
  fprintf fmt "    let r := mod_gt a b in\n";
  fprintf fmt "    match compare r zero with\n";
  fprintf fmt "    | Gt => cont r (mod_gt b r)\n";
  fprintf fmt "    | _ => b\n";
  fprintf fmt "    end\n";
  fprintf fmt "  | _ => a\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Fixpoint gcd_gt (p:positive) (cont:%s->%s->%s) (a b:%s) {struct p} : %s :=\n" t t t t t;
  fprintf fmt "  gcd_gt_body a b\n";
  fprintf fmt "    (fun a b =>\n";
  fprintf fmt "       match p with\n";
  fprintf fmt "       | xH => cont a b\n";
  fprintf fmt "       | xO p => gcd_gt p (gcd_gt p cont) a b\n";
  fprintf fmt "       | xI p => gcd_gt p (gcd_gt p cont) a b\n"; 
  fprintf fmt "       end).\n";
  fprintf fmt "\n";

  fprintf fmt " Definition gcd_cont a b :=\n";
  fprintf fmt "  match compare one b with\n";
  fprintf fmt "  | Eq => one\n";
  fprintf fmt "  | _ => a\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition gcd a b :=\n";
  fprintf fmt "  match compare a b with\n";
  fprintf fmt "  | Eq => a\n";
  fprintf fmt "  | Lt => gcd_gt (digits b) gcd_cont b a\n";
  fprintf fmt "  | Gt => gcd_gt (digits a) gcd_cont a b\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt "Definition pheight p := Peano.pred (nat_of_P (get_height w0_op.(znz_digits) (plength p))).";
  fprintf fmt "\n";

  fprintf fmt " Definition of_pos x :=\n";
  fprintf fmt "  let h := pheight x in\n"; 
  fprintf fmt "  match h with\n";
  let rec print_S s fmt i =
   if i = 0 then fprintf fmt "%s" s
   else fprintf fmt "(S %a)" (print_S s) (i-1)
  in
  for i = 0 to size do
    fprintf fmt "  | ";
    print_S "O" fmt i;
    fprintf fmt " => %s%i (snd (w%i_op.(znz_of_pos) x))\n" "reduce_" i i
  done;
  fprintf fmt "  | _ =>\n";
  fprintf fmt "    let n := minus h %i in\n" (size+1);
  fprintf fmt "    %sn n (snd ((make_op n).(znz_of_pos) x))\n" "reduce_";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition of_N x :=\n";
  fprintf fmt "  match x with\n";
  fprintf fmt "  | BinNat.N0 => zero\n";
  fprintf fmt "  | Npos p => of_pos p\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition to_Z x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx => w%i_op.(znz_to_Z) wx\n" c i i
  done;
  fprintf fmt "  | %sn n wx => (make_op n).(znz_to_Z) wx\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


 (* Head0 *)
  fprintf fmt " Definition head0 w := match w with\n";
  for i = 0 to size do
    fprintf fmt " | %s%i w=> reduce_%i (w%i_op.(znz_head0) w)\n"  c i i i;
  done;
  fprintf fmt " | %sn n w=> reduce_n n ((make_op n).(znz_head0) w)\n" c;
  fprintf fmt " end.\n";
  fprintf fmt "\n";

 (* Tail0 *)
  fprintf fmt " Definition tail0 w := match w with\n";
  for i = 0 to size do
    fprintf fmt " | %s%i w=> reduce_%i (w%i_op.(znz_tail0) w)\n"  c i i i;
  done;
  fprintf fmt " | %sn n w=> reduce_n n ((make_op n).(znz_tail0) w)\n" c;
  fprintf fmt " end.\n";
  fprintf fmt "\n";

  (* Number of digits *)
  fprintf fmt " Definition %sdigits x :=\n" c;
  fprintf fmt "  match x with\n";
  fprintf fmt "  | %s0 _ => %s0 w0_op.(znz_zdigits)\n" c c;
  for i = 1 to size do 
    fprintf fmt "  | %s%i _ => reduce_%i w%i_op.(znz_zdigits)\n" c i i i;
  done;
  fprintf fmt "  | %sn n _ => reduce_n n (make_op n).(znz_zdigits)\n \n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


  fprintf fmt " Definition level ";
  for i = 0 to size do 
    fprintf fmt "f%i " i;
  done;
  fprintf fmt " fn x y: %s_ :=  match x, y with\n" t;
  fprintf fmt "  | %s0 wx, %s0 wy => f0 wx wy \n" c c;
  for j = 1 to size do 
    fprintf fmt "  | %s0 wx, %s%i wy => f%i "  c c j j;
    if j = 1 then fprintf fmt "(WW w_0 wx) wy\n"
    else fprintf fmt "(extend%i w0 (WW w_0 wx)) wy\n" (j-1)
  done;
  fprintf fmt "  | %s0 wx, %sn n wy =>\n" c c; 
  fprintf fmt "    fn n (extend n w%i (extend%i w0 (WW w_0 wx))) wy\n"
    size size;
  for i = 1 to size do
    fprintf fmt "  | %s%i wx, %s0 wy =>\n" c i c;
    fprintf fmt 
     "    f%i wx " i;
    if i = 1 then fprintf fmt "(WW w_0 wy)\n"
    else fprintf fmt "(extend%i w0 (WW w_0 wy))\n" (i-1);
    for j = 1 to size do
      fprintf fmt "  | %s%i wx, %s%i wy => " c i c j;
      if i < j then fprintf fmt "f%i (extend%i w%i wx) wy\n" j (j-i) (i-1)
      else if i = j then  fprintf fmt "f%i wx wy\n" j 
      else fprintf fmt "f%i wx (extend%i w%i wy)\n" i (i-j) (j-1)
    done;
    fprintf fmt   
      "  | %s%i wx, %sn n wy => fn n (extend n w%i (extend%i w%i wx)) wy\n" 
      c i c size (size-i+1) (i-1)
  done;
  fprintf fmt "  | %sn n wx, %s0 wy =>\n" c c; 
  fprintf fmt "    fn n wx (extend n w%i (extend%i w0 (WW w_0 wy)))\n" 
    size size;
  for j = 1 to size do
    fprintf fmt 
      "  | %sn n wx, %s%i wy => fn n wx (extend n w%i (extend%i w%i wy))\n"
       c c j size (size-j+1) (j-1); 
  done; 
  fprintf fmt "  | %sn n wx, %sn m wy =>\n" c c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "     fn mn\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d)))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

 (* Shiftr *)
  for i = 0 to size do
    fprintf fmt " Definition shiftr%i n x := w%i_op.(znz_add_mul_div) (w%i_op.(znz_sub) w%i_op.(znz_zdigits) n) w%i_op.(znz_0) x.\n" i i i i i;
  done;
  fprintf fmt " Definition shiftrn n p x := (make_op n).(znz_add_mul_div) ((make_op n).(znz_sub) (make_op n).(znz_zdigits) p) (make_op n).(znz_0) x.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition shiftr := \n";
  fprintf fmt "  Eval lazy beta delta [level] in \n";
  fprintf fmt "     level (fun n x => %s0 (shiftr0 n x))\n" c;
  for i = 1 to size do
  fprintf fmt "           (fun n x => reduce_%i (shiftr%i n x))\n" i i;
  done;
  fprintf fmt "           (fun n p x => reduce_n n (shiftrn n p x)).\n";
  fprintf fmt "\n";


  fprintf fmt " Definition safe_shiftr n x := \n";
  fprintf fmt "   match compare n (Ndigits x) with\n ";
  fprintf fmt "   |  Lt => shiftr n x \n";
  fprintf fmt "   | _ => %s0 w_0\n" c;
  fprintf fmt "   end.\n";
  fprintf fmt "\n";

 (* Shiftl *)
  for i = 0 to size do
    fprintf fmt " Definition shiftl%i n x := w%i_op.(znz_add_mul_div) n x w%i_op.(znz_0).\n" i i i
  done;
  fprintf fmt " Definition shiftln n p x := (make_op n).(znz_add_mul_div) p x (make_op n).(znz_0).\n";
  fprintf fmt " Definition shiftl := \n";
  fprintf fmt "  Eval lazy beta delta [level] in \n";
  fprintf fmt "     level (fun n x => %s0 (shiftl0 n x))\n" c;
  for i = 1 to size do
  fprintf fmt "           (fun n x => reduce_%i (shiftl%i n x))\n" i i;
  done;
  fprintf fmt "           (fun n p x => reduce_n n (shiftln n p x)).\n";
  fprintf fmt "\n";
  fprintf fmt "\n";

 (* Double size *)
  fprintf fmt " Definition double_size w := match w with\n";
  fprintf fmt " | %s0 w=> N1 (WW w_0 w)\n" c;
  for i = 1 to size-1 do
    fprintf fmt " | %s%i w=> %s%i (extend1 _ w)\n"  c i c (i + 1);
  done;
  fprintf fmt " | %s%i w=> %sn 0 (extend1 _ w)\n" c size c ;
  fprintf fmt " | %sn n w=> %sn (S n) (extend1 _ w)\n" c c;
  fprintf fmt " end.\n";
  fprintf fmt "\n";

 (* Safe shiftl *)

  fprintf fmt " Definition safe_shiftl_aux_body cont n x :=\n";
  fprintf fmt "   match compare n (head0 x)  with\n";
  fprintf fmt "      Gt => cont n (double_size x)\n";
  fprintf fmt "   |  _ => shiftl n x\n";
  fprintf fmt "   end.\n";
  fprintf fmt "\n";
  fprintf fmt " Fixpoint safe_shiftl_aux p cont n x  {struct p} :=\n";
  fprintf fmt "   safe_shiftl_aux_body \n";
  fprintf fmt "       (fun n x => match p with\n";
  fprintf fmt "        | xH => cont n x\n";
  fprintf fmt "        | xO p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x\n";
  fprintf fmt "        | xI p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x\n";
  fprintf fmt "        end) n x.\n";
  fprintf fmt "\n";
  fprintf fmt "  Definition safe_shiftl n x :=\n";
  fprintf fmt "  safe_shiftl_aux (digits n) (fun n x => %s0 w0_op.(znz_0)) n x.\n" c;
  fprintf fmt " \n";

  (* even *)
  fprintf fmt " Definition is_even x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx => w%i_op.(znz_is_even) wx\n" c i i
  done;
  fprintf fmt "  | %sn n wx => (make_op n).(znz_is_even) wx\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


  fprintf fmt "(* Proof section *)\n";
  fprintf fmt "\n";

  if gen_proof1 then
  begin
  fprintf fmt " Let w0_spec: znz_spec w0_op := W0.w_spec.\n";
  for i = 1 to 3 do
    fprintf fmt " Let w%i_spec: znz_spec w%i_op := mk_znz2_spec w%i_spec.\n" i i (i-1) 
  done;
  for i = 4 to size + 3 do
    fprintf fmt " Let w%i_spec : znz_spec w%i_op := mk_znz2_karatsuba_spec w%i_spec.\n" i i (i-1)
  done;
  fprintf fmt "\n";

  fprintf fmt " Theorem make_op_S: forall n,\n";
  fprintf fmt "   make_op (S n) = mk_zn2z_op_karatsuba (make_op n).\n";
  fprintf fmt " intro n; pattern n; apply lt_wf_ind; clear n.\n";
  fprintf fmt " intros n; case n; clear n.\n";
  fprintf fmt "   intros _; unfold make_op, make_op_aux, w%i_op; apply refl_equal.\n" (size + 2);
  fprintf fmt " intros n; case n; clear n.\n";
  fprintf fmt "   intros _; unfold make_op, make_op_aux, w%i_op; apply refl_equal.\n" (size + 3);
  fprintf fmt " intros n; case n; clear n.\n";
  fprintf fmt "   intros _; unfold make_op, make_op_aux, w%i_op, w%i_op; apply refl_equal.\n" (size + 3) (size + 2);
  fprintf fmt " intros n Hrec.\n";
  fprintf fmt "   change (make_op (S (S (S (S n))))) with\n";
  fprintf fmt "          (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (make_op (S n))))).\n";
  fprintf fmt "   change (make_op (S (S (S n)))) with\n";
  fprintf fmt "         (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (make_op n)))).\n";
  fprintf fmt "   rewrite Hrec; auto with arith.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";

  fprintf fmt " Let wn_spec: forall n, znz_spec (make_op n).\n";
  fprintf fmt "  intros n; elim n; clear n.\n";
  fprintf fmt "    exact w%i_spec.\n" (size + 1);
  fprintf fmt "  intros n Hrec; rewrite make_op_S.\n";
  fprintf fmt "  exact (mk_znz2_karatsuba_spec Hrec).\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";
  end;

  fprintf fmt " Open Scope Z_scope.\n";
  fprintf fmt " Notation \"[ x ]\" := (to_Z x).\n";
  fprintf fmt " \n";

  if gen_proof2 then
  begin
  for i = 1 to size + 1 do
    fprintf fmt " Let znz_to_Z_%i: forall x y,\n" i;
    fprintf fmt "   znz_to_Z w%i_op (WW x y) = \n" i;
    fprintf fmt "    znz_to_Z w%i_op x * base (znz_digits w%i_op) + znz_to_Z w%i_op y.\n" (i-1) (i-1) (i-1);
    fprintf fmt " Proof.\n";
    fprintf fmt " auto.\n";
    fprintf fmt " Qed. \n";
    fprintf fmt "\n";
  done;

  fprintf fmt " Let znz_to_Z_n: forall n x y,\n";
  fprintf fmt "   znz_to_Z (make_op (S n)) (WW x y) = \n";
  fprintf fmt "    znz_to_Z (make_op n) x * base (znz_digits (make_op n)) + znz_to_Z (make_op n) y.\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n x y; rewrite make_op_S; auto.\n";
  fprintf fmt " Qed. \n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Theorem succ_spec: forall n, [succ n] = [n] + 1.\n";
  if gen_proof3 then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt "  intros n; case n; unfold succ, to_Z.\n";
  for i = 0 to size do
     fprintf fmt  "  intros n1; generalize (spec_succ_c w%i_spec n1);\n" i;
     fprintf fmt  "  unfold succ, to_Z, w%i_succ_c; case znz_succ_c; auto.\n" i;
     fprintf fmt  "     intros ww H; rewrite <- H.\n";
     fprintf fmt "     (rewrite znz_to_Z_%i; unfold interp_carry;\n" (i + 1);
     fprintf fmt "           apply f_equal2 with (f := Zplus); auto;\n";
     fprintf fmt "           apply f_equal2 with (f := Zmult); auto;\n";
     fprintf fmt "           exact (spec_1 w%i_spec)).\n" i;
  done;
  fprintf fmt "  intros k n1; generalize (spec_succ_c (wn_spec k) n1).\n";
  fprintf fmt "  unfold succ, to_Z; case znz_succ_c; auto.\n";
  fprintf fmt "  intros ww H; rewrite <- H.\n";
  fprintf fmt "     (rewrite (znz_to_Z_n k); unfold interp_carry;\n";
  fprintf fmt "           apply f_equal2 with (f := Zplus); auto;\n";
  fprintf fmt "           apply f_equal2 with (f := Zmult); auto;\n";
  fprintf fmt "           exact (spec_1 (wn_spec k))).\n";
  fprintf fmt " Qed.\n ";
  end else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  if gen_proof4 then
  begin
  for i = 0 to size do
    fprintf fmt " Let spec_w%i_add: forall x y, [w%i_add x y] = [%s%i x] + [%s%i y].\n" i i c i c i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros n m; unfold to_Z, w%i_add, w%i_add_c.\n" i i;
    fprintf fmt "  generalize (spec_add_c w%i_spec n m); case znz_add_c; auto.\n" i;
    fprintf fmt " intros ww H; rewrite <- H.\n"; 
    fprintf fmt "    rewrite znz_to_Z_%i; unfold interp_carry;\n" (i + 1);
    fprintf fmt "    apply f_equal2 with (f := Zplus); auto;\n";
    fprintf fmt "    apply f_equal2 with (f := Zmult); auto;\n";
    fprintf fmt "    exact (spec_1 w%i_spec).\n" i;
    fprintf fmt " Qed.\n";
    fprintf fmt " Hint Rewrite spec_w%i_add: addr.\n" i;
    fprintf fmt "\n";
  done;
  fprintf fmt " Let spec_wn_add: forall n x y, [addn n x y] = [%sn n x] + [%sn n y].\n" c c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros k n m; unfold to_Z, addn.\n";
  fprintf fmt "  generalize (spec_add_c (wn_spec k) n m); case znz_add_c; auto.\n";
  fprintf fmt " intros ww H; rewrite <- H.\n"; 
  fprintf fmt " rewrite (znz_to_Z_n k); unfold interp_carry;\n";
  fprintf fmt "        apply f_equal2 with (f := Zplus); auto;\n";
  fprintf fmt "        apply f_equal2 with (f := Zmult); auto;\n";
  fprintf fmt "        exact (spec_1 (wn_spec k)).\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_wn_add: addr.\n";
  fprintf fmt "\n";

  for i = 0 to size do
    fprintf fmt " Let spec_w%i_eq0: forall x, if w%i_eq0 x then [%s%i x] = 0 else True.\n" i i c i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros x; unfold w%i_eq0.\n" i;
    fprintf fmt "  generalize (spec_eq0 w%i_spec x); case znz_eq0; auto.\n" i;
    fprintf fmt " Qed.\n";
    fprintf fmt "\n";
  done;

  fprintf fmt " Let spec_extendn_0: forall n wx, [%sn n (extend n _ wx)] = [%sn 0 wx].\n" c c;
  fprintf fmt " intros n; elim n; auto.\n";
  fprintf fmt " intros n1 Hrec wx; simpl extend; rewrite <- Hrec; auto.\n";
  fprintf fmt " unfold to_Z.\n";
  fprintf fmt " case n1; auto; intros n2; repeat rewrite make_op_S; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_extendn_0: extr.\n";
  fprintf fmt "\n";
  fprintf fmt " Let spec_extendn0_0: forall n wx, [%sn (S n) (WW W0 wx)] = [%sn n wx].\n" c c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n x; unfold to_Z.\n";
  fprintf fmt " rewrite znz_to_Z_n.\n";
  fprintf fmt " rewrite <- (Zplus_0_l (znz_to_Z (make_op n) x)).\n";
  fprintf fmt " apply (f_equal2 Zplus); auto.\n";
  fprintf fmt " case n; auto.\n";
  fprintf fmt " intros n1; rewrite make_op_S; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_extendn_0: extr.\n";
  fprintf fmt "\n";
  fprintf fmt " Let spec_extend_tr: forall m n (w: word _ (S n)),\n";
  fprintf fmt " [%sn (m + n) (extend_tr w m)] = [%sn n w].\n" c c;
  fprintf fmt " Proof.\n";
  fprintf fmt " induction m; auto.\n";
  fprintf fmt " intros n x; simpl extend_tr.\n";
  fprintf fmt " simpl plus; rewrite spec_extendn0_0; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_extend_tr: extr.\n";
  fprintf fmt "\n";
  fprintf fmt " Let spec_cast_l: forall n m x1,\n";
  fprintf fmt " [%sn (Max.max n m)\n" c;
  fprintf fmt " (castm (diff_r n m) (extend_tr x1 (snd (diff n m))))] =\n";
  fprintf fmt " [%sn n x1].\n" c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n m x1; case (diff_r n m); simpl castm.\n";
  fprintf fmt " rewrite spec_extend_tr; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_cast_l: extr.\n";
  fprintf fmt "\n";
  fprintf fmt " Let spec_cast_r: forall n m x1,\n";
  fprintf fmt " [%sn (Max.max n m)\n" c;
  fprintf fmt "  (castm (diff_l n m) (extend_tr x1 (fst (diff n m))))] =\n";
  fprintf fmt " [%sn m x1].\n" c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n m x1; case (diff_l n m); simpl castm.\n";
  fprintf fmt " rewrite spec_extend_tr; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_cast_r: extr.\n";
  fprintf fmt "\n";

  fprintf fmt " Let spec_extend0_0: forall wx, [%s1 (WW w_0 wx)] = [%s0 wx].\n" c c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; unfold to_Z.\n";
  fprintf fmt " rewrite <- (Zplus_0_l (znz_to_Z w0_op x)).\n";
  fprintf fmt " rewrite znz_to_Z_1.\n";
  fprintf fmt " rewrite <- (Zmult_0_l (base (znz_digits w0_op))).\n";
  fprintf fmt " apply (f_equal2 Zplus); auto.\n";
  fprintf fmt " apply (f_equal2 Zmult); auto.\n";
  fprintf fmt " exact (spec_0 w0_spec); auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_extend0_0: extr.\n";
  fprintf fmt " \n";

  for i = 1 to size do
    for j = 1 to size - i do
    fprintf fmt " Let spec_extend%i_%i: forall wx, [%s%i (extend%i _ wx)] = [%s%i wx].\n" i j c (i + j) i c j;
    fprintf fmt " Proof.
  intros x; unfold extend%i, to_Z.\n" i;
    fprintf fmt " rewrite <- (Zplus_0_l (znz_to_Z w%i_op x)).\n" j;
    fprintf fmt " rewrite znz_to_Z_%i; auto.\n" (i + j);
    fprintf fmt " Qed.\n";
    fprintf fmt " Hint Rewrite spec_extend%i_%i: extr.\n" i j;
    fprintf fmt "\n";
    done;
  fprintf fmt " Let spec_extend%i_0: forall wx, [%sn 0 (extend%i _ wx)] = [N%i wx].\n" i c i (size + 1 - i);
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; unfold extend%i, to_Z; auto.\n" (size + 1 - i);
  fprintf fmt " Qed.\n";
  fprintf fmt " Hint Rewrite spec_extend%i_0: extr.\n" i;
  fprintf fmt " \n";

  done;
  end;

  fprintf fmt " Theorem spec_add: forall x y, [add x y] = [x] + [y].\n";
  if gen_proof5 then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x y; case x; unfold add.\n";
  fprintf fmt " intros x1; case y.\n";
  fprintf fmt "     intros y1; rewrite spec_w0_add; auto.\n";
  for i = 1 to size do 
    fprintf fmt "     intros y1; generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.\n";
    fprintf fmt "       rewrite HH; auto.\n";
    if i = 1 then
      fprintf fmt "     rewrite spec_w1_add; rewrite spec_extend0_0; auto.\n"
    else 
      fprintf fmt "     rewrite spec_w%i_add; rewrite spec_extend%i_1; rewrite spec_extend0_0; auto.\n" i (i -1);
  done;
  fprintf fmt " intros n y1; generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.\n";
  fprintf fmt " rewrite HH; auto.\n";
  fprintf fmt " rewrite spec_wn_add.\n";
  fprintf fmt " rewrite spec_extendn_0; rewrite spec_extend%i_0; rewrite spec_extend0_0; auto.\n" size;
  for i = 1 to size do
    fprintf fmt " intros x1; case y.\n";
    fprintf fmt "   intros y1; generalize (spec_w0_eq0 y1); case w0_eq0; intros HH.\n";
    fprintf fmt "     rewrite HH; rewrite Zplus_0_r; auto.\n";
    if i = 1 then
      fprintf fmt "   rewrite spec_w1_add; rewrite spec_extend0_0; auto.\n"
    else
      fprintf fmt "   rewrite spec_w%i_add; rewrite spec_extend%i_1; rewrite spec_extend0_0; auto.\n" i (i-1);
    for j = 1 to size do
      if i <= j then
        fprintf fmt " intros y1; rewrite spec_w%i_add; auto.\n" j
      else
        fprintf fmt " intros y1; rewrite spec_w%i_add; auto.\n" i;
    done;
    fprintf fmt " intros n y1; rewrite spec_wn_add.\n";
    fprintf fmt " rewrite spec_extendn_0; rewrite spec_extend%i_0; auto.\n" (size + 1 - i);
  done;
  fprintf fmt " intros n x1; case y.\n";
  fprintf fmt "   intros y1; generalize (spec_w0_eq0 y1); case w0_eq0; intros HH.\n";
  fprintf fmt "     rewrite HH; rewrite Zplus_0_r; auto.\n";
  fprintf fmt "   rewrite spec_wn_add; rewrite spec_extendn_0; \n";
  fprintf fmt "      rewrite spec_extend%i_0; rewrite spec_extend0_0; auto.\n" size;
  for i = 1 to size do
    fprintf fmt "  intros y1; rewrite spec_wn_add; rewrite spec_extendn_0; rewrite spec_extend%i_0; auto.\n" (size + 1 - i);
  done;
  fprintf fmt " intros m y1; rewrite spec_wn_add; rewrite spec_cast_l; rewrite spec_cast_r; auto.\n";
  fprintf fmt " Qed.\n";
  end else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  if gen_proof6 then
  begin
  fprintf fmt " Let spec_reduce_0: forall x, [reduce_0 x] = [%s0 x].\n" c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; unfold to_Z, reduce_0.\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";

  for i = 1 to size + 1 do
   if (i == size + 1) then
    fprintf fmt " Let spec_reduce_%i: forall x, [reduce_%i x] = [%sn 0 x].\n" i i c
   else
    fprintf fmt " Let spec_reduce_%i: forall x, [reduce_%i x] = [%s%i x].\n" i i c i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros x; case x; unfold reduce_%i.\n" i;
    fprintf fmt " exact (spec_0 w0_spec).\n";
    fprintf fmt " intros x1 y1.\n";
    fprintf fmt " generalize (spec_w%i_eq0 x1); \n" (i - 1);
    fprintf fmt "   case w%i_eq0; intros H1; auto.\n" (i - 1);
    if i <> 1 then 
      fprintf fmt " rewrite spec_reduce_%i.\n" (i - 1);
    fprintf fmt " unfold to_Z; rewrite znz_to_Z_%i.\n" i;
    fprintf fmt " unfold to_Z in H1; rewrite H1; auto.\n";
    fprintf fmt " Qed.\n";
    fprintf fmt " \n";
  done;

  fprintf fmt " Let spec_reduce_n: forall n x, [reduce_n n x] = [%sn n x].\n" c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n; elim n; simpl reduce_n.\n";
  fprintf fmt "   intros x; rewrite <- spec_reduce_%i; auto.\n" (size + 1);
  fprintf fmt " intros n1 Hrec x; case x.\n";
  fprintf fmt " unfold to_Z; rewrite make_op_S; auto.\n";
  fprintf fmt " exact (spec_0 w0_spec).\n";
  fprintf fmt " intros x1 y1; case x1; auto.\n";
  fprintf fmt " rewrite Hrec.\n";
  fprintf fmt " rewrite spec_extendn0_0; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";

  fprintf fmt "  Let to_Z_pos: forall x, 0 <= [x].\n";
  fprintf fmt "  Proof.\n";
  fprintf fmt "  intros x; case x; unfold to_Z.\n";
  for i = 0 to size do
    fprintf fmt "  intros x1; case (spec_to_Z w%i_spec x1); auto.\n" i;
  done;
  fprintf fmt "  intros n x1; case (spec_to_Z (wn_spec n) x1); auto.\n";
  fprintf fmt "  Qed.\n";
  fprintf fmt "  \n";

  fprintf fmt " Let spec_pred: forall x, 0 < [x] -> [pred x] = [x] - 1.\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold pred.\n";
  for i = 0 to size do
    fprintf fmt " intros x1 H1; unfold w%i_pred_c; \n" i;
    fprintf fmt " generalize (spec_pred_c w%i_spec x1); case znz_pred_c; intros y1.\n" i;
    fprintf fmt " rewrite spec_reduce_%i; auto.\n" i;
    fprintf fmt " unfold interp_carry; unfold to_Z.\n";
    fprintf fmt " case (spec_to_Z w%i_spec x1); intros HH1 HH2.\n" i;
    fprintf fmt " case (spec_to_Z w%i_spec y1); intros HH3 HH4 HH5.\n" i;
    fprintf fmt " assert (znz_to_Z w%i_op x1 - 1 < 0); auto with zarith.\n" i;
    fprintf fmt " unfold to_Z in H1; auto with zarith.\n";
  done;
  fprintf fmt " intros n x1 H1;  \n";
  fprintf fmt "   generalize (spec_pred_c (wn_spec n) x1); case znz_pred_c; intros y1.\n";
  fprintf fmt "   rewrite spec_reduce_n; auto.\n";
  fprintf fmt " unfold interp_carry; unfold to_Z.\n";
  fprintf fmt " case (spec_to_Z (wn_spec n) x1); intros HH1 HH2.\n";
  fprintf fmt " case (spec_to_Z (wn_spec n) y1); intros HH3 HH4 HH5.\n";
  fprintf fmt " assert (znz_to_Z (make_op n) x1 - 1 < 0); auto with zarith.\n";
  fprintf fmt " unfold to_Z in H1; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";

  fprintf fmt " Let spec_pred0: forall x, [x] = 0 -> [pred x] = 0.\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold pred.\n";
  for i = 0 to size do
    fprintf fmt " intros x1 H1; unfold w%i_pred_c; \n" i;
    fprintf fmt "   generalize (spec_pred_c w%i_spec x1); case znz_pred_c; intros y1.\n" i;
    fprintf fmt " unfold interp_carry; unfold to_Z.\n";
    fprintf fmt " unfold to_Z in H1; auto with zarith.\n";
    fprintf fmt " case (spec_to_Z w%i_spec y1); intros HH3 HH4; auto with zarith.\n" i;
    fprintf fmt " intros; exact (spec_0 w0_spec).\n";
  done;
  fprintf fmt " intros n x1 H1; \n";
  fprintf fmt "   generalize (spec_pred_c (wn_spec n) x1); case znz_pred_c; intros y1.\n";
  fprintf fmt " unfold interp_carry; unfold to_Z.\n";
  fprintf fmt " unfold to_Z in H1; auto with zarith.\n";
  fprintf fmt " case (spec_to_Z (wn_spec n) y1); intros HH3 HH4; auto with zarith.\n";
  fprintf fmt " intros; exact (spec_0 w0_spec).\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";

  for i = 0 to size do
    fprintf fmt " Let spec_w%i_sub: forall x y, [%s%i y] <= [%s%i x] -> [w%i_sub x y] = [%s%i x] - [%s%i y].\n" i c i c i i c i c i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros n m; unfold w%i_sub, w%i_sub_c.\n" i i;
    fprintf fmt "  generalize (spec_sub_c w%i_spec n m); case znz_sub_c; \n" i;
    if i == 0 then 
      fprintf fmt "    intros x; auto.\n"
    else
      fprintf fmt "   intros x; try rewrite spec_reduce_%i; auto.\n" i;
    fprintf fmt " unfold interp_carry; unfold zero, w_0, to_Z.\n";
    fprintf fmt " rewrite (spec_0 w0_spec).\n";
    fprintf fmt " case (spec_to_Z w%i_spec x); intros; auto with zarith.\n" i;
    fprintf fmt " Qed.\n";
    fprintf fmt "\n";
  done;

  fprintf fmt " Let spec_wn_sub: forall n x y, [%sn n y] <= [%sn n x] -> [subn n x y] = [%sn n x] - [%sn n y].\n" c c c c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros k n m; unfold subn.\n";
  fprintf fmt " generalize (spec_sub_c (wn_spec k) n m); case znz_sub_c; \n";
  fprintf fmt "   intros x; auto.\n";
  fprintf fmt " unfold interp_carry, to_Z.\n";
  fprintf fmt " case (spec_to_Z (wn_spec k) x); intros; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Theorem spec_sub: forall x y, [y] <= [x] -> [sub x y] = [x] - [y].\n";
  if gen_proof7 then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x y; case x; unfold sub.\n";
  fprintf fmt " intros x1; case y.\n";
  fprintf fmt "     intros y1 H; rewrite spec_w0_sub; auto.\n";
  for i = 1 to size do 
    fprintf fmt "     intros y1 H; generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.\n";
    fprintf fmt "       generalize H; rewrite HH; unfold to_Z, zero, w_0.\n";
    fprintf fmt "       rewrite (spec_0 w0_spec); case (spec_to_Z w%i_spec y1); auto with zarith.\n" i;
    if i == 1 then
      fprintf fmt "     rewrite spec_w1_sub; rewrite spec_extend0_0; auto.\n" 
    else
      fprintf fmt "     rewrite spec_w%i_sub; rewrite spec_extend%i_1; rewrite spec_extend0_0; auto.\n" i (i - 1);
  done;
  fprintf fmt " intros n y1 H; generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.\n";
  fprintf fmt "   generalize H; rewrite HH; unfold to_Z, zero, w_0.\n";
  fprintf fmt "   rewrite (spec_0 w0_spec); case (spec_to_Z (wn_spec n) y1); auto with zarith.\n";
  fprintf fmt " rewrite spec_wn_sub; rewrite spec_extendn_0; rewrite spec_extend%i_0; rewrite spec_extend0_0; auto.\n" size;
  for i = 1 to size do
    fprintf fmt " intros x1; case y.\n";
    fprintf fmt "   intros y1 H; generalize (spec_w0_eq0 y1); case w0_eq0; intros HH.\n";
    fprintf fmt "     rewrite HH; rewrite Zminus_0_r; auto.\n";
    if i = 1 then
      fprintf fmt "   rewrite spec_w1_sub; rewrite spec_extend0_0; auto.\n"
    else
      fprintf fmt "   rewrite spec_w%i_sub; rewrite spec_extend%i_1; rewrite spec_extend0_0; auto.\n" i (i-1);
    for j = 1 to size do
      if i <= j then
        fprintf fmt " intros y1 H; rewrite spec_w%i_sub; auto.\n" j
      else
        fprintf fmt " intros y1 H; rewrite spec_w%i_sub; auto.\n" i;
    done;
    fprintf fmt " intros n y1 H; rewrite spec_wn_sub;\n";
    fprintf fmt "   rewrite spec_extendn_0; rewrite spec_extend%i_0; auto.\n" (size + 1 - i);
  done;
  fprintf fmt " intros n x1; case y.\n";
  fprintf fmt "   intros y1 H; generalize (spec_w0_eq0 y1); case w0_eq0; intros HH.\n";
  fprintf fmt "     rewrite HH; rewrite Zminus_0_r; auto.\n";
  fprintf fmt "   rewrite spec_wn_sub; rewrite spec_extendn_0; \n";
  fprintf fmt "      rewrite spec_extend%i_0; rewrite spec_extend0_0; auto.\n" size;
  for i = 1 to size do
    fprintf fmt "  intros y1 H; rewrite spec_wn_sub; rewrite spec_extendn_0; rewrite spec_extend%i_0; auto.\n" (size + 1 - i);
  done;
  fprintf fmt " intros m y1 H; rewrite spec_wn_sub; rewrite spec_cast_l; rewrite spec_cast_r; auto.\n";
  fprintf fmt " Qed.\n";
  end else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  if gen_proof8 then
  begin
  for i = 0 to size do
    fprintf fmt " Let spec_w%i_sub0: forall x y, [%s%i x] < [%s%i y] -> [w%i_sub x y] = 0.\n" i c i c i i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros n m; unfold w%i_sub, w%i_sub_c.\n" i i;
    fprintf fmt "  generalize (spec_sub_c w%i_spec n m); case znz_sub_c; \n" i;
    fprintf fmt "   intros x; unfold interp_carry.\n";
    fprintf fmt "   unfold to_Z; case (spec_to_Z w%i_spec x); intros; auto with zarith.\n" i;
    fprintf fmt " intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.\n";
    fprintf fmt " Qed.\n";
    fprintf fmt "\n";
  done;

  fprintf fmt " Let spec_wn_sub0: forall n x y, [%sn n x] < [%sn n y] -> [subn n x y] = 0.\n" c c;
  fprintf fmt " Proof.\n";
  fprintf fmt " intros k n m; unfold subn.\n";
  fprintf fmt " generalize (spec_sub_c (wn_spec k) n m); case znz_sub_c; \n";
  fprintf fmt "   intros x; unfold interp_carry.\n";
  fprintf fmt "   unfold to_Z; case (spec_to_Z (wn_spec k) x); intros; auto with zarith.\n";
  fprintf fmt " intros; unfold to_Z, w_0; rewrite (spec_0 (w0_spec)); auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Theorem spec_sub0: forall x y, [x] < [y] -> [sub x y] = 0.\n";
  if gen_proof9 then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x y; case x; unfold sub.\n";
  fprintf fmt " intros x1; case y.\n";
  fprintf fmt "     intros y1 H; rewrite spec_w0_sub0; auto.\n";
  for i = 1 to size do 
    fprintf fmt "     intros y1 H; generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.\n";
    fprintf fmt "       unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.\n";
    if i == 1 then
      fprintf fmt "     apply spec_w1_sub0; rewrite spec_extend0_0; auto.\n" 
    else
      fprintf fmt "     apply spec_w%i_sub0; rewrite spec_extend%i_1; rewrite spec_extend0_0; auto.\n" i (i - 1);
  done;
  fprintf fmt " intros n y1 H; generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.\n";
  fprintf fmt "   unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.\n";
  fprintf fmt " apply spec_wn_sub0; rewrite spec_extendn_0; rewrite spec_extend%i_0; rewrite spec_extend0_0; auto.\n" size;
  for i = 1 to size do
    fprintf fmt " intros x1; case y.\n";
    fprintf fmt "   intros y1 H; generalize (spec_w0_eq0 y1); case w0_eq0; intros HH.\n";
    fprintf fmt "     generalize H; rewrite HH; unfold to_Z; case (spec_to_Z w%i_spec x1); auto with zarith.\n" i;
    if i = 1 then
      fprintf fmt "   apply spec_w1_sub0; rewrite spec_extend0_0; auto.\n"
    else
      fprintf fmt "   apply spec_w%i_sub0; rewrite spec_extend%i_1; rewrite spec_extend0_0; auto.\n" i (i-1);
    for j = 1 to size do
      if i <= j then
        fprintf fmt " intros y1 H; apply spec_w%i_sub0; auto.\n" j
      else
        fprintf fmt " intros y1 H; apply spec_w%i_sub0; auto.\n" i;
    done;
    fprintf fmt " intros n y1 H; apply spec_wn_sub0;\n";
    fprintf fmt "   rewrite spec_extendn_0; rewrite spec_extend%i_0; auto.\n" (size + 1 - i);
  done;
  fprintf fmt " intros n x1; case y.\n";
  fprintf fmt "   intros y1 H; generalize (spec_w0_eq0 y1); case w0_eq0; intros HH.\n";
  fprintf fmt "    generalize H; rewrite HH; unfold to_Z; case (spec_to_Z (wn_spec n) x1); auto with zarith.\n";
  fprintf fmt "   apply spec_wn_sub0; rewrite spec_extendn_0; \n";
  fprintf fmt "      rewrite spec_extend%i_0; rewrite spec_extend0_0; auto.\n" size;
  for i = 1 to size do
    fprintf fmt "  intros y1 H; apply spec_wn_sub0; rewrite spec_extendn_0; rewrite spec_extend%i_0; auto.\n" (size + 1 - i);
  done;
  fprintf fmt " intros m y1 H; apply spec_wn_sub0; rewrite spec_cast_l; rewrite spec_cast_r; auto.\n";
  fprintf fmt " Qed.\n"
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  if gen_proof10 then
  begin

  fprintf fmt " Fixpoint nmake_op (ww:Set) (ww_op: znz_op ww) (n: nat) : \n";
  fprintf fmt "       znz_op (word ww n) :=\n";
  fprintf fmt "  match n return znz_op (word ww n) with \n";
  fprintf fmt "   O => ww_op\n";
  fprintf fmt "  | S n1 => mk_zn2z_op (nmake_op ww ww_op n1) \n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
  fprintf fmt " Let nmake_op0 := nmake_op _ w0_op.\n";
  fprintf fmt "\n";
  fprintf fmt " Theorem nmake_op_S: forall ww (w_op: znz_op ww) x, \n";
  fprintf fmt "   nmake_op _ w_op (S x) = mk_zn2z_op (nmake_op _ w_op x).\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  fprintf fmt " Theorem nmake_op0_S:  forall x,\n";
  fprintf fmt "   nmake_op0 (S x) = mk_zn2z_op (nmake_op0 x).\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  fprintf fmt " Theorem digits_0: znz_digits w0_op = znz_digits (nmake_op0 0).\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  fprintf fmt " Theorem nmake_0: znz_to_Z w0_op = znz_to_Z (nmake_op0 0).\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";

  for i = 1 to size do
    fprintf fmt " Theorem digits_%i: znz_digits w%i_op = znz_digits (nmake_op0 %i).\n" i i i;
  fprintf fmt " rewrite nmake_op0_S; unfold w%i_op.\n" i;
  if i <= 3 then 
    fprintf fmt " rewrite digits_zop; rewrite digits_%i.\n" (i  - 1)
  else
    fprintf fmt " rewrite digits_kzop; rewrite digits_%i.\n" (i  - 1);
  fprintf fmt " rewrite <- digits_zop; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  fprintf fmt " Theorem nmake_%i: znz_to_Z w%i_op = znz_to_Z (nmake_op0 %i).\n" i i i;
  fprintf fmt " rewrite nmake_op0_S; unfold w%i_op.\n" i;
  if i <= 3 then
    fprintf fmt " rewrite make_zop; rewrite digits_%i; rewrite nmake_%i.\n" (i - 1) (i -1)
    else
    fprintf fmt " rewrite make_kzop; rewrite digits_%i; rewrite nmake_%i.\n" (i - 1) (i -1);
  fprintf fmt " rewrite <- make_zop; auto.\n";
  fprintf fmt " Qed.\n";
  done;

  fprintf fmt " Let gen_digits: forall n, \n";
  fprintf fmt "   base (znz_digits (make_op n)) = (GenBase.gen_wB (znz_digits w%i_op) (S n)).\n" size;
  fprintf fmt " intros n; elim n; clear n.\n";
  fprintf fmt " unfold make_op, make_op_aux; unfold w%i_op; unfold word.\n" (size + 1);
  fprintf fmt " rewrite digits_kzop.\n";
  fprintf fmt " unfold GenBase.gen_wB, GenBase.gen_digits; auto.\n";

  fprintf fmt " intros n Hrec; rewrite make_op_S.\n";
  fprintf fmt " change (%sznz_digits (word w%i (S (S n))) (mk_zn2z_op_karatsuba (make_op n))) with (xO (znz_digits (make_op n))).\n" "@" size;
  fprintf fmt " rewrite base_xO; rewrite Hrec.\n";
  fprintf fmt " unfold GenBase.gen_wB; rewrite <- base_xO; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";
  fprintf fmt " Let gen_make: forall n y, GenBase.gen_to_Z (znz_digits w%i_op) (znz_to_Z w%i_op) (S n) y =\n" size size;
  fprintf fmt "      znz_to_Z (make_op n) y.\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n; elim n; auto.\n";
  fprintf fmt " intros n1 Hrec y; case y; auto.\n";
  fprintf fmt "  rewrite make_op_S; auto.\n";
  fprintf fmt " intros yh yl; rewrite znz_to_Z_n.\n";
  fprintf fmt " rewrite gen_digits.\n";
  fprintf fmt " rewrite <- Hrec; rewrite <- Hrec; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem digits_gend:forall n ww (w_op: znz_op ww), \n";
  fprintf fmt "    znz_digits (nmake_op _ w_op n) = \n";
  fprintf fmt "    GenBase.gen_digits (znz_digits w_op) n.\n";
  fprintf fmt " Proof.";
  fprintf fmt " intros n; elim n; auto; clear n.\n";
  fprintf fmt " intros n Hrec ww ww_op; simpl GenBase.gen_digits.\n";
  fprintf fmt " rewrite <- Hrec; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  fprintf fmt " Theorem nmake_gen: forall n ww (w_op: znz_op ww), \n";
  fprintf fmt "    znz_to_Z (nmake_op _ w_op n) =\n";
  fprintf fmt "    %sGenBase.gen_to_Z _ (znz_digits w_op) (znz_to_Z w_op) n.\n" "@";
  fprintf fmt " Proof.";
  fprintf fmt " intros n; elim n; auto; clear n.\n";
  fprintf fmt " intros n Hrec ww ww_op; simpl GenBase.gen_to_Z; unfold zn2z_to_Z.\n";
  fprintf fmt " rewrite <- Hrec; auto.\n";
  fprintf fmt " unfold GenBase.gen_wB; rewrite <- digits_gend; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";



  fprintf fmt " Theorem digits_clean: forall ww (w_op1 w_op2: znz_op ww) n, \n";
  fprintf fmt "     znz_digits w_op1 = znz_digits w_op2 ->\n";
  fprintf fmt "     znz_digits (nmake_op _ w_op1 n) = znz_digits (nmake_op _ w_op2 n).\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros ww w_op1 w_op2 n; elim n; auto; clear n.\n";
  fprintf fmt " intros n Hrec H1.\n";
  fprintf fmt " simpl; unfold zn2z_to_Z; rewrite Hrec; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";
  fprintf fmt " Theorem nmake_clean: forall ww (w_op1 w_op2: znz_op ww) n, \n";
  fprintf fmt "     znz_digits w_op1 = znz_digits w_op2 ->\n";
  fprintf fmt "     znz_to_Z w_op1 = znz_to_Z w_op2 ->\n";
  fprintf fmt "     znz_to_Z (nmake_op _ w_op1 n) =\n";
  fprintf fmt "     znz_to_Z (nmake_op _ w_op2 n).\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros ww w_op1 w_op2 n; elim n; auto; clear n.\n";
  fprintf fmt " intros n Hrec H1 H2.\n";
  fprintf fmt " generalize (digits_clean _ _ _ n H1).\n";
  fprintf fmt " simpl; unfold zn2z_to_Z; intros H3.\n";
  fprintf fmt " rewrite Hrec; auto; rewrite H3; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";

  for i = 2 to size do
    for j = 1 to i - 1 do
      fprintf fmt " Let digits_%i_%i: znz_digits (nmake_op _ w%i_op %i) = znz_digits (nmake_op _ w0_op %i).\n" j (i - j) j (i - j) i;
      fprintf fmt " Proof.\n";
      fprintf fmt " replace (nmake_op _ w0_op %i) with (nmake_op _ (nmake_op _ w0_op %i) %i).\n" i j (i - j);
      fprintf fmt " generalize (digits_clean _ _ _ %i digits_%i).\n" (i- j) j;
      fprintf fmt " unfold nmake_op0; auto.\n";
      fprintf fmt " unfold nmake_op; auto.\n";
      fprintf fmt " Qed.\n";
      fprintf fmt "\n";
    done
   done;

  for i = 2 to size do
    for j = 1 to i - 1 do
      fprintf fmt " Let nmake_op_%i_%i: znz_to_Z (nmake_op _ w%i_op %i) = znz_to_Z (nmake_op _ w0_op %i).\n" j (i - j) j (i - j) i;
      fprintf fmt " Proof.\n";
      fprintf fmt " replace (nmake_op _ w0_op %i) with (nmake_op _ (nmake_op _ w0_op %i) %i).\n" i j (i - j);
      fprintf fmt " generalize (nmake_clean _ _ _ %i digits_%i nmake_%i).\n" (i- j) j j;
      fprintf fmt " unfold nmake_op0; auto.\n";
      fprintf fmt " unfold nmake_op; auto.\n";
      fprintf fmt " Qed.\n";
      fprintf fmt "\n";
    done
   done
  end;

  (* Comparison *)
  fprintf fmt " Theorem spec_compare: forall x y,\n";
  fprintf fmt "    match compare x y with \n";
  fprintf fmt "      Eq => [x] = [y]\n";
  fprintf fmt "    | Lt => [x] < [y]\n";
  fprintf fmt "    | Gt => [x] > [y]\n";
  fprintf fmt "    end.\n";
  fprintf fmt " Proof.\n";
  if gen_proof11 then
  begin
  for i= 0 to size do
    fprintf fmt " assert(F1_%i:= (spec_0 w%i_spec)).\n" i i;
    fprintf fmt " assert(F2_%i:= (spec_compare w%i_spec (znz_0 w%i_op))).\n" i  i i;
    fprintf fmt " assert(F3_%i:= (spec_to_Z w%i_spec)).\n" i i;
    fprintf fmt " assert(F4_%i:= (spec_compare w%i_spec)).\n" i i;
  done;
  fprintf fmt " intros x; case x; clear x; unfold compare, to_Z.\n";
  for i = 0 to size do
    fprintf fmt "  intros x y; case y; clear y; auto.\n";
    for j = 0 to i - 1 do
      fprintf fmt "    intros y; unfold comparen_%i, w_0, compare_%i.\n" j j;
      fprintf fmt "      replace (znz_to_Z w%i_op x) with (%sGenBase.gen_to_Z w%i (znz_digits w%i_op) (znz_to_Z w%i_op) %i x).\n" i "@" j j j (i -j);
      fprintf fmt "      apply spec_compare_mn_1; auto.\n";
      fprintf fmt "      rewrite <- nmake_gen; rewrite nmake_%i. \n" i;
      if (i == 0) || (j == 0) then
        fprintf fmt "      unfold nmake_op0; auto.\n"
      else
        fprintf fmt "      rewrite nmake_op_%i_%i; unfold nmake_op0, nmake_op; auto.\n" j (i - j);
    done;
    fprintf fmt "  exact (spec_compare w%i_spec x).\n" i;
    for j = i + 1  to size do
      fprintf fmt "    intros y; apply spec_opp; unfold comparen_%i, w_0, compare_%i.\n" i i;
      fprintf fmt "      replace (znz_to_Z w%i_op y) with (%sGenBase.gen_to_Z w%i (znz_digits w%i_op) (znz_to_Z w%i_op) %i y). \n" j "@" i i i (j - i);
      fprintf fmt "      apply spec_compare_mn_1; auto.\n";
      fprintf fmt "      rewrite <- nmake_gen; rewrite nmake_%i.\n" j;
      if (i == 0)  then
         fprintf fmt "     unfold nmake_op0; auto.\n"
       else
        fprintf fmt "      rewrite nmake_op_%i_%i; unfold nmake_op0, nmake_op; auto.\n" i (j - i);
    done;
    fprintf fmt "    intros n y; apply spec_opp; unfold comparen_%i, w%i, w_0, compare_0.\n" i i;
    fprintf fmt "    rewrite <- gen_make.\n";
    fprintf fmt "    apply spec_compare_mn_1; auto.\n";
    if i <> size then
    begin
     fprintf fmt "      try rewrite (spec_0 w%i_spec); auto.\n" i;
     fprintf fmt "      intros x1 y1.\n";
     fprintf fmt "        replace (znz_to_Z w%i_op x1) with (%sGenBase.gen_to_Z w%i (znz_digits w%i_op) (znz_to_Z w%i_op) %i x1).\n" size "@" i i i (size - i);
     fprintf fmt "        apply spec_compare_mn_1; auto.\n";
     fprintf fmt "        rewrite <- nmake_gen; rewrite nmake_%i.\n" size;
     if (i == 0)  then
        fprintf fmt "        unfold nmake_op0; auto.\n"
      else
        fprintf fmt "      rewrite nmake_op_%i_%i; unfold nmake_op0, nmake_op; auto.\n" i (size - i);
     fprintf fmt "       intros x1; case (F3_%i x1); split; auto.\n" i;
     fprintf fmt "       apply Zlt_trans with (1 := H0); unfold base; apply ZPowerAux.Zpower_lt_monotone.\n";
     fprintf fmt "         auto with zarith.\n";
     fprintf fmt "       split; [red; intro HH; discriminate HH | idtac].\n";
     fprintf fmt "       apply length_pos_lt.\n";
     fprintf fmt "       change (length_pos (znz_digits w%i_op)) with\n" size;
     fprintf fmt "             (S(%i + (length_pos (znz_digits w%i_op))))%snat.\n" (size - i - 1) i "%";
     fprintf fmt "       apply le_lt_n_Sm; apply le_plus_r.\n";
   end;
  done;
  fprintf fmt "  intros n x y; case y; clear y.\n";
  for i = 0 to size do
    fprintf fmt "    intros y; rewrite <- gen_make; unfold comparen_%i; apply spec_compare_mn_1; auto.\n" i;
    if i <> size then
    begin
     fprintf fmt "    unfold w_0; try rewrite (spec_0 w%i_spec); auto.\n" i;
     fprintf fmt "    intros x1 y1.\n";
     fprintf fmt "      replace (znz_to_Z w%i_op x1) with (%sGenBase.gen_to_Z w%i (znz_digits w%i_op) (znz_to_Z w%i_op) %i x1).\n" size "@" i i i (size - i);
     fprintf fmt "      apply spec_compare_mn_1; auto.\n";
     fprintf fmt "        rewrite <- nmake_gen; rewrite nmake_%i.\n" size;
     if (i == 0)  then
        fprintf fmt "        unfold nmake_op0; auto.\n"
      else
        fprintf fmt "      rewrite nmake_op_%i_%i; unfold nmake_op0, nmake_op; auto.\n" i (size - i);
     fprintf fmt "      intros x1; case (F3_%i x1); split; auto.\n" i;
     fprintf fmt "      apply Zlt_trans with (1 := H0); unfold base; apply ZPowerAux.Zpower_lt_monotone.\n";
     fprintf fmt "        auto with zarith.\n";
     fprintf fmt "      split; [red; intro HH; discriminate HH | idtac].\n";
     fprintf fmt "      apply length_pos_lt.\n";
     fprintf fmt "      change (length_pos (znz_digits w%i_op)) with\n" size;
     fprintf fmt "             (S(%i + (length_pos (znz_digits w%i_op))))%snat.\n" (size - i - 1) i "%";
     fprintf fmt "     apply le_lt_n_Sm; apply le_plus_r.\n";
    end
  done;
  fprintf fmt "    intros m y.\n";
  fprintf fmt "      generalize (spec_cast_l n m x); simpl to_Z; simpl word; intros HH; rewrite <- HH; clear HH.\n";
  fprintf fmt "      generalize (spec_cast_r n m y); simpl to_Z; simpl word; intros HH; rewrite <- HH; clear HH.\n";
  fprintf fmt "      apply (spec_compare (wn_spec (Max.max n m))).\n";
  fprintf fmt " Qed.\n";
  end else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  if gen_proof12 then
  begin
  for i = 0 to size do
    fprintf fmt " Let spec_w%i_mul_add: forall x y z,\n" i;
    fprintf fmt "  let (q,r) := w%i_mul_add x y z in\n" i;
    fprintf fmt "  znz_to_Z w%i_op q * (base (znz_digits w%i_op))  +  znz_to_Z w%i_op r =\n" i i i;
    fprintf fmt "  znz_to_Z w%i_op x * znz_to_Z w%i_op y + znz_to_Z w%i_op z :=\n" i i i ;
    fprintf fmt "   (spec_mul_add w%i_spec).\n" i;
    fprintf fmt "\n";
  done;
  for i = 0 to size do


    fprintf fmt " Theorem spec_w%i_mul_add_n1: forall n x y z,\n" i;
    fprintf fmt "  let (q,r) := w%i_mul_add_n1 n x y z in\n" i;
    fprintf fmt "  znz_to_Z w%i_op q * (base (znz_digits (nmake_op _ w%i_op n)))  +\n" i i;
    fprintf fmt "  znz_to_Z (nmake_op _ w%i_op n) r =\n" i;
    fprintf fmt "  znz_to_Z (nmake_op _ w%i_op n) x * znz_to_Z w%i_op y +\n" i i;
    fprintf fmt "  znz_to_Z w%i_op z.\n" i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros n x y z; unfold w%i_mul_add_n1.\n" i;
    fprintf fmt " rewrite nmake_gen.\n";
    fprintf fmt " rewrite digits_gend.\n";
    fprintf fmt " change (base (GenBase.gen_digits (znz_digits w%i_op) n)) with\n" i;
    fprintf fmt "        (GenBase.gen_wB (znz_digits w%i_op) n).\n" i;
    fprintf fmt " apply spec_gen_mul_add_n1; auto.\n";
    if i == 0 then fprintf fmt " exact (spec_0 w%i_spec).\n" i;
    fprintf fmt " exact (spec_WW w%i_spec).\n" i;
    fprintf fmt " exact (spec_0W w%i_spec).\n" i;
    fprintf fmt " exact (spec_mul_add w%i_spec).\n" i;
    fprintf fmt " Qed.\n";
    fprintf fmt "\n";
  done;
  end;

  fprintf fmt " Theorem spec_mul: forall x y, [mul x y] =[x] * [y].\n";
  fprintf fmt " Proof.\n";
  if gen_proof13 then
   begin
  fprintf fmt "  intros x; case x; clear x.\n";
  fprintf fmt "    intros x y; case y; clear y; unfold mul.\n";
  fprintf fmt "    intros y; rewrite spec_reduce_1; unfold to_Z.\n";
  fprintf fmt "     generalize (spec_mul_c w0_spec x y).\n";
  fprintf fmt "     intros HH; rewrite <- HH; clear HH; auto.\n";

  fprintf fmt "   intros y; unfold zero, w0_eq0, w_0.\n";
  fprintf fmt "     generalize (spec_eq0 w0_spec x); case znz_eq0.\n";
  fprintf fmt "     unfold to_Z; intros HH; rewrite HH; auto.\n";
  fprintf fmt "       rewrite (spec_0 w0_spec); auto.\n";
  fprintf fmt "     intros _.\n";
  fprintf fmt "       generalize (spec_w0_mul_add_n1 1 y x (znz_0 w0_op)); case w0_mul_add_n1.\n";
  fprintf fmt "       intros yh yl.\n";
  fprintf fmt "         generalize (spec_eq0 w0_spec yh); case znz_eq0.\n";
  fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
  fprintf fmt "           unfold to_Z; rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
  fprintf fmt "           rewrite nmake_1; rewrite nmake_0; unfold nmake_op0.\n";
  fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH.\n";
  fprintf fmt "           auto.\n";
  fprintf fmt "         intros _.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
  fprintf fmt "           unfold to_Z; rewrite nmake_1; rewrite nmake_0; unfold nmake_op0.\n";
  fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH.\n";
  fprintf fmt "           rewrite znz_to_Z_2; rewrite znz_to_Z_1.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite nmake_1; rewrite nmake_0; rewrite digits_1; unfold nmake_op0; auto.\n";


  for j = 2 to size - 1 do
    fprintf fmt "   intros y; unfold zero, w0_eq0, w_0.\n";
    fprintf fmt "     generalize (spec_eq0 w0_spec x); case znz_eq0.\n";
    fprintf fmt "     unfold to_Z; intros HH; rewrite HH; auto.\n";
    fprintf fmt "       rewrite (spec_0 w0_spec); auto.\n";
    fprintf fmt "     intros _.\n";
    fprintf fmt "       generalize (spec_w0_mul_add_n1 %i y x (znz_0 w0_op)); case w0_mul_add_n1.\n" j;
    fprintf fmt "       intros yh yl.\n";
    fprintf fmt "         generalize (spec_eq0 w0_spec yh); case znz_eq0.\n";
    fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
    fprintf fmt "           unfold to_Z; rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
    fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" j;
    fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH.\n";
    fprintf fmt "           auto.\n";
    fprintf fmt "         intros _.\n";
    fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
    fprintf fmt "           unfold to_Z; rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" j;
    fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH; clear HH.\n";
    fprintf fmt "           rewrite znz_to_Z_%i.\n" (j + 1);
    fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) yh)); unfold to_Z.\n" (j - 1);
    fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
    fprintf fmt "           rewrite znz_to_Z_1.\n";
    fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
    fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; rewrite digits_%i; unfold nmake_op0; auto.\n" j j;

  done;

  fprintf fmt "   intros y; unfold to_Z, zero, w0_eq0, w_0.\n";
  fprintf fmt "     generalize (spec_eq0 w0_spec x); case znz_eq0.\n";
  fprintf fmt "     intros HH; rewrite HH; auto.\n";
  fprintf fmt "       rewrite (spec_0 w0_spec); auto.\n";
  fprintf fmt "     intros _.\n";
  fprintf fmt "       generalize (spec_w0_mul_add_n1 %i y x (znz_0 w0_op)); case w0_mul_add_n1.\n" size;
  fprintf fmt "       intros yh yl.\n";
  fprintf fmt "         generalize (spec_eq0 w0_spec yh); case znz_eq0.\n";
  fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
  fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" size;
  fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH.\n";
  fprintf fmt "           auto.\n";
  fprintf fmt "         intros _.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
  fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" size;
  fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH; clear HH.\n";
  fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
  fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) yh)); unfold to_Z.\n" (size - 1);
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite znz_to_Z_1.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; rewrite digits_%i; unfold nmake_op0; auto.\n" size size;
  fprintf fmt "   intros n y; unfold to_Z, zero, w0_eq0, w_0.\n";
  fprintf fmt "     generalize (spec_eq0 w0_spec x); case znz_eq0.\n";
  fprintf fmt "     intros HH; rewrite HH; auto.\n";
  fprintf fmt "       rewrite (spec_0 w0_spec); auto.\n";
  fprintf fmt "     intros _.\n";
  fprintf fmt "       generalize (spec_w%i_mul_add_n1 (S n) y (extend%i w0 (WW (znz_0 w0_op) x)) W0); case w%i_mul_add_n1.\n" size (size - 1) size;
  fprintf fmt "       intros yh yl.\n";
  fprintf fmt "         rewrite Zplus_0_r.\n";
  fprintf fmt "         unfold w%i_eq0; generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" size size;
  fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
  fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) x)); unfold to_Z.\n" (size - 1);
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite Zmult_comm; rewrite znz_to_Z_1.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
  fprintf fmt "         intros _.\n";
  fprintf fmt "           rewrite (znz_to_Z_n n).\n";
  fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) x)); unfold to_Z.\n" (size - 1);
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite znz_to_Z_1.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           generalize (spec_extendn_0 n (WW W0 yh)); unfold to_Z.\n";
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
  fprintf fmt "           rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           rewrite digits_gend.\n";
  fprintf fmt "           rewrite gen_digits; unfold GenBase.gen_wB.\n";
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite Zmult_comm; auto.\n";
  
  for i = 1 to size do
    fprintf fmt "   intros x y; case y; clear y; unfold mul.\n";
    if i = 1 then 
      begin
        fprintf fmt "   intros y; unfold to_Z, zero, w0_eq0, w_0.\n";
        fprintf fmt "     generalize (spec_eq0 w0_spec y); case znz_eq0.\n";
        fprintf fmt "     intros HH; rewrite HH; auto; clear HH.\n";
        fprintf fmt "       rewrite (spec_0 w0_spec); rewrite Zmult_0_r; auto.\n";
        fprintf fmt "     intros _.\n";
        fprintf fmt "       generalize (spec_w0_mul_add_n1 1 x y (znz_0 w0_op)); case w0_mul_add_n1.\n";
        fprintf fmt "       intros yh yl.\n";
        fprintf fmt "         generalize (spec_eq0 w0_spec yh); case znz_eq0.\n";
        fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
        fprintf fmt "           rewrite nmake_1; rewrite nmake_0; unfold nmake_op0.\n";
        fprintf fmt "           intros HH; rewrite <- HH.\n";
        fprintf fmt "           auto.\n";
        fprintf fmt "         intros _.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
        fprintf fmt "           rewrite nmake_1; rewrite nmake_0; unfold nmake_op0.\n";
        fprintf fmt "           intros HH; rewrite <- HH.\n";
        fprintf fmt "           rewrite znz_to_Z_2; rewrite znz_to_Z_1.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
        fprintf fmt "           rewrite nmake_1; rewrite nmake_0; rewrite digits_1; unfold nmake_op0; auto.\n";
      end
    else if i = size then 
      begin
        fprintf fmt "   intros y; unfold to_Z, zero, w0_eq0, w_0.\n";
        fprintf fmt "     generalize (spec_eq0 w0_spec y); case znz_eq0.\n";
        fprintf fmt "     intros HH; rewrite HH; auto; clear HH.\n";
        fprintf fmt "       rewrite (spec_0 w0_spec); rewrite Zmult_0_r; auto.\n";
        fprintf fmt "     intros _.\n";
        fprintf fmt "       generalize (spec_w0_mul_add_n1 %i x y (znz_0 w0_op)); case w0_mul_add_n1.\n" size;
        fprintf fmt "       intros yh yl.\n";
        fprintf fmt "         generalize (spec_eq0 w0_spec yh); case znz_eq0.\n";
        fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
        fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" size;
        fprintf fmt "           intros HH; rewrite <- HH.\n";
        fprintf fmt "           auto.\n";
        fprintf fmt "         intros _.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
        fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" size;
        fprintf fmt "           intros HH; rewrite <- HH; clear HH.\n";
        fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
        fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) yh)); unfold to_Z.\n" (size - 1);
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite znz_to_Z_1.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
        fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; rewrite digits_%i; unfold nmake_op0; auto.\n" size size;
      end
    else
      begin
        fprintf fmt "   intros y; unfold to_Z, zero, w0_eq0, w_0.\n";
        fprintf fmt "     generalize (spec_eq0 w0_spec y); case znz_eq0.\n";
        fprintf fmt "     intros HH; rewrite HH; auto; clear HH.\n";
        fprintf fmt "       rewrite (spec_0 w0_spec); rewrite Zmult_0_r; auto.\n";
        fprintf fmt "     intros _.\n";
        fprintf fmt "       generalize (spec_w0_mul_add_n1 %i x y (znz_0 w0_op)); case w0_mul_add_n1.\n" i;
        fprintf fmt "       intros yh yl.\n";
        fprintf fmt "         generalize (spec_eq0 w0_spec yh); case znz_eq0.\n";
        fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
        fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" i;
        fprintf fmt "           intros HH; rewrite <- HH.\n";
        fprintf fmt "           auto.\n";
        fprintf fmt "         intros _.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n";
        fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; unfold nmake_op0.\n" i;
        fprintf fmt "           intros HH; rewrite <- HH; clear HH.\n";
        fprintf fmt "           rewrite znz_to_Z_%i.\n" (i + 1);
        fprintf fmt "           generalize (spec_extend%i_%i (WW (znz_0 w0_op) yh)); unfold to_Z.\n" (i - 1) 1;
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite znz_to_Z_1.\n";
        fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
        fprintf fmt "           rewrite nmake_%i; rewrite nmake_0; rewrite digits_%i; unfold nmake_op0; auto.\n" i i;
      end;
    for j = 1 to size do
 fprintf fmt "  (* i = %i j = %i *)\n" i j;
      if i = j then
        begin
          fprintf fmt "   intros y; unfold to_Z.\n";
          fprintf fmt "     generalize (spec_mul_c w%i_spec x y).\n" i;
          fprintf fmt "     intros HH; rewrite <- HH; clear HH; auto.\n";
        end 
      else 
        begin
	let min,max, wmin, wmax = 
	  if i < j then i, j, "x", "y" else j, i, "y", "x" in
	if max = size then
          begin
            fprintf fmt "   intros y; unfold to_Z, zero, w%i_eq0, w_0.\n" min;
            fprintf fmt "       generalize (spec_w%i_mul_add_n1 %i %s %s W0); case w%i_mul_add_n1.\n" min (max -min) wmax wmin min;
            fprintf fmt "       intros yh yl.\n";
            fprintf fmt "         generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" min;
            fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
            fprintf fmt "           rewrite Zplus_0_r.\n";
            fprintf fmt "           rewrite nmake_%i; rewrite nmake_%i; unfold nmake_op0.\n" max min;
            fprintf fmt "           rewrite nmake_op_%i_%i.\n" min (max - min);
            if i = min then
              fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH; clear HH.\n"
            else
              fprintf fmt "           intros HH; rewrite <- HH; clear HH.\n";
            fprintf fmt "           auto.\n";
            fprintf fmt "         intros _.\n";
            fprintf fmt "           rewrite Zplus_0_r.\n";
            fprintf fmt "           rewrite nmake_%i; rewrite nmake_%i; unfold nmake_op0.\n" max min;
            fprintf fmt "           rewrite nmake_op_%i_%i.\n" min (max - min);
            if i = min then
              fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH; clear HH.\n"
            else
              fprintf fmt "           intros HH; rewrite <- HH; clear HH.\n";
            fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (max + 1);
            fprintf fmt "           generalize (spec_extend%i_%i yh); unfold to_Z.\n" (max - min) min;
            fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
            fprintf fmt "           rewrite nmake_%i; rewrite digits_%i; unfold nmake_op0.\n" min max;
            fprintf fmt "           rewrite nmake_%i; unfold nmake_op0.\n" max;
            fprintf fmt "           rewrite digits_%i_%i; auto.\n" min (max - min);
          end
	else 
          begin
            fprintf fmt "   intros y; unfold to_Z, zero, w0_eq0, w_0.\n";
            fprintf fmt "       generalize (spec_w%i_mul_add_n1 %i %s %s W0); case w%i_mul_add_n1.\n" min (max - min) wmax wmin min;
            fprintf fmt "       intros yh yl.\n";
            fprintf fmt "         unfold w%i_eq0; generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" min min;
            fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
            fprintf fmt "           rewrite Zplus_0_r.\n";
            fprintf fmt "           rewrite nmake_%i; rewrite nmake_%i; unfold nmake_op0.\n" max min;
            if i = min then
              fprintf fmt "           rewrite Zmult_comm; rewrite nmake_op_%i_%i; auto.\n" min (max - min)
            else
              fprintf fmt "           rewrite nmake_op_%i_%i; auto.\n" min (max - min);
            fprintf fmt "         intros _.\n";
            fprintf fmt "           rewrite Zplus_0_r.\n";
            fprintf fmt "           rewrite digits_%i_%i.\n" min (max - min);
            fprintf fmt "           rewrite nmake_%i; rewrite nmake_%i; unfold nmake_op0.\n" min max;
            fprintf fmt "           rewrite nmake_op_%i_%i.\n" min (max - min);
            if i = min then
              fprintf fmt "           intros HH; rewrite Zmult_comm; rewrite <- HH; clear HH.\n"
            else
              fprintf fmt "           intros HH; rewrite <- HH; clear HH.\n";
            fprintf fmt "           rewrite znz_to_Z_%i.\n" (max + 1);
            fprintf fmt "           generalize (spec_extend%i_%i yh); unfold to_Z.\n" (max - min) min;
            fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
            fprintf fmt "           rewrite nmake_%i; rewrite nmake_%i; rewrite digits_%i; unfold nmake_op0; auto.\n" min max max;
          end
      end
    done;
    if i = size then 
      begin
        fprintf fmt "   intros n y; unfold to_Z, zero, w%i_eq0, w_0.\n" size;
        fprintf fmt "       generalize (spec_w%i_mul_add_n1 (S n) y x W0); case w%i_mul_add_n1.\n" size size;
        fprintf fmt "       intros yh yl.\n";
        fprintf fmt "         rewrite Zplus_0_r.\n";
        fprintf fmt "         generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" size;
        fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite Zmult_comm.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
        fprintf fmt "         intros _.\n";
        fprintf fmt "           rewrite (znz_to_Z_n n).\n";
        fprintf fmt "           generalize (spec_extendn_0 n (WW W0 yh)); unfold to_Z.\n";
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
        fprintf fmt "           rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
        fprintf fmt "           rewrite digits_gend.\n";
        fprintf fmt "           rewrite gen_digits; unfold GenBase.gen_wB.\n";
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite Zmult_comm; auto.\n";
      end
    else
      begin
        fprintf fmt "   intros n y; unfold to_Z, zero, w%i_eq0, w_0.\n" size;
        fprintf fmt "       generalize (spec_w%i_mul_add_n1 (S n) y (extend%i _ x) W0); case w%i_mul_add_n1.\n" size (size - i) size;
        fprintf fmt "       intros yh yl.\n";
        fprintf fmt "         rewrite Zplus_0_r.\n";
        fprintf fmt "         unfold w%i_eq0; generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" size size;
        fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
        fprintf fmt "           generalize (spec_extend%i_%i x); unfold to_Z.\n" (size -i) i;
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite Zmult_comm.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
        fprintf fmt "         intros _.\n";
        fprintf fmt "           rewrite (znz_to_Z_n n).\n";
        fprintf fmt "           generalize (spec_extend%i_%i x); unfold to_Z.\n" (size - i) i;
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           generalize (spec_extendn_0 n (WW W0 yh)); unfold to_Z.\n";
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
        fprintf fmt "           rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
        fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
        fprintf fmt "           rewrite digits_gend.\n";
        fprintf fmt "           rewrite gen_digits; unfold GenBase.gen_wB.\n";
        fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
        fprintf fmt "           rewrite Zmult_comm; auto.\n";
      end;    
  done;

  fprintf fmt "   intros n x y; case y; clear y; unfold mul.\n";
  fprintf fmt "   intros y; unfold to_Z, zero, w0_eq0, w%i_eq0, w_0.\n" size;
  fprintf fmt "     generalize (spec_eq0 w0_spec y); case znz_eq0.\n";
  fprintf fmt "     intros HH; rewrite HH; auto; clear HH.\n";
  fprintf fmt "       rewrite (spec_0 w0_spec); rewrite Zmult_0_r; auto.\n";
  fprintf fmt "     intros _.\n";
  fprintf fmt "       generalize (spec_w%i_mul_add_n1 (S n) x (extend%i w0 (WW (znz_0 w0_op) y)) W0); case w%i_mul_add_n1.\n" size (size - 1) size;
  fprintf fmt "       intros yh yl.\n";
  fprintf fmt "         generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" size;
  fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
  fprintf fmt "           rewrite Zplus_0_r.\n";
  fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) y)); unfold to_Z.\n" (size - 1);
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite znz_to_Z_1.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
  fprintf fmt "         intros _.\n";
  fprintf fmt "           rewrite Zplus_0_r.\n";
  fprintf fmt "           generalize (spec_extend%i_1 (WW (znz_0 w0_op) y)); unfold to_Z.\n" (size - 1);
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           rewrite znz_to_Z_1.\n";
  fprintf fmt "           rewrite (spec_0 w0_spec); rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite (znz_to_Z_n n).\n";
  fprintf fmt "           generalize (spec_extendn_0 n (WW W0 yh)); unfold to_Z.\n";
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
  fprintf fmt "           rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
  fprintf fmt "           rewrite nmake_%i; rewrite nmake_0;  unfold nmake_op0.\n" size;
  fprintf fmt "           intros HH; rewrite <- HH; clear HH.\n";
  fprintf fmt "           rewrite digits_gend; rewrite gen_digits; auto.\n";
  
  for j = 1 to size - 1 do
    fprintf fmt "   intros y; unfold to_Z, zero, w%i_eq0, w_0.\n" size;
    fprintf fmt "       generalize (spec_w%i_mul_add_n1 (S n) x (extend%i _ y) W0); case w%i_mul_add_n1.\n" size (size - j) size;
    fprintf fmt "       intros yh yl.\n";
    fprintf fmt "         generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" size;
    fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
    fprintf fmt "           rewrite Zplus_0_r.\n";
    fprintf fmt "           rewrite nmake_%i; rewrite nmake_%i; unfold nmake_op0.\n" size j;
    fprintf fmt "           generalize (spec_extend%i_%i y); unfold to_Z.\n" (size - j) j;
    fprintf fmt "           rewrite nmake_%i; unfold nmake_op0.\n" size;
    fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
    fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
    fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
    fprintf fmt "           rewrite nmake_%i; unfold nmake_op0; auto.\n" j;
    fprintf fmt "         intros _.\n";
    fprintf fmt "           rewrite Zplus_0_r.\n";
    fprintf fmt "           generalize (spec_extend%i_%i y); unfold to_Z.\n" (size - j) j;
    fprintf fmt "           rewrite nmake_%i; unfold nmake_op0.\n" size;
    fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
    fprintf fmt "           rewrite (znz_to_Z_n n).\n";
    fprintf fmt "           generalize (spec_extendn_0 n (WW W0 yh)); unfold to_Z.\n";
    fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
    fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
    fprintf fmt "           rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
    fprintf fmt "           rewrite digits_gend; rewrite gen_digits; auto.\n";
    fprintf fmt "           rewrite nmake_%i; unfold nmake_op0; auto.\n" size;
    fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
    fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
  done;
  fprintf fmt "   intros y; unfold to_Z, zero, w%i_eq0, w_0.\n" size;
  fprintf fmt "       generalize (spec_w%i_mul_add_n1 (S n) x y W0); case w%i_mul_add_n1.\n" size size;
  fprintf fmt "       intros yh yl.\n";
  fprintf fmt "         generalize (spec_eq0 w%i_spec yh); case znz_eq0.\n" size;
  fprintf fmt "         intros HH; rewrite HH; auto; rewrite Zmult_0_l; rewrite Zplus_0_l; clear HH.\n";
  fprintf fmt "           rewrite Zplus_0_r.\n";
  fprintf fmt "           rewrite nmake_%i; unfold nmake_op0.\n" size;
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
  fprintf fmt "         intros _.\n";
  fprintf fmt "           rewrite Zplus_0_r.\n";
  fprintf fmt "           rewrite nmake_%i; unfold nmake_op0.\n" size;
  fprintf fmt "           rewrite (znz_to_Z_n n).\n";
  fprintf fmt "           generalize (spec_extendn_0 n (WW W0 yh)); unfold to_Z.\n";
  fprintf fmt "           intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "           simpl make_op; rewrite znz_to_Z_%i.\n" (size + 1);
  fprintf fmt "           rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "           rewrite digits_gend; rewrite gen_digits; auto.\n";
  fprintf fmt "           rewrite nmake_%i; unfold nmake_op0; auto.\n" size;
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen.\n";
  fprintf fmt "           rewrite <- gen_make; rewrite <- nmake_gen; auto.\n";
  fprintf fmt "    intros m y.\n";
  fprintf fmt "    rewrite spec_reduce_n.\n";
  fprintf fmt "    unfold to_Z.\n";
  fprintf fmt "    generalize (spec_mul_c (wn_spec (Max.max n m))\n";
  fprintf fmt "                (castm (diff_r n m)\n";
  fprintf fmt "                 (extend_tr x (snd (diff n m))))\n";
  fprintf fmt "                (castm (diff_l n m)\n";
  fprintf fmt "                 (extend_tr y (fst (diff n m)))));\n";
  fprintf fmt "       case znz_mul_c.\n";
  fprintf fmt "    generalize (spec_cast_l n m x); simpl to_Z; simpl word; intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "    generalize (spec_cast_r n m y); simpl to_Z; simpl word; intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "    rewrite make_op_S; auto.\n";
  fprintf fmt "    intros x1 y1.\n";
  fprintf fmt "    rewrite (znz_to_Z_n (Max.max n m)).\n";
  fprintf fmt "    generalize (spec_cast_l n m x); simpl to_Z; simpl word; intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "    generalize (spec_cast_r n m y); simpl to_Z; simpl word; intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "    simpl zn2z_to_Z; auto.\n";
  fprintf fmt "    Qed.\n";
  end
  
  else
    fprintf fmt " Admitted.\n";    
  fprintf fmt "\n";    

  fprintf fmt " Theorem spec_sqrt : forall x,\n";
  fprintf fmt "       [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.\n";
  fprintf fmt " Proof.\n";
  if gen_proof14 then
  begin
  fprintf fmt " intros x; case x; unfold sqrt.\n";
  for i = 0 to size do
    fprintf fmt "   intros y; rewrite spec_reduce_%i.\n" i;
    fprintf fmt "   unfold to_Z, w%i_sqrt.\n" i;
    fprintf fmt "   exact (spec_sqrt w%i_spec y).\n" i;
  done;
  fprintf fmt "   intros n y; rewrite spec_reduce_n.\n";
  fprintf fmt "   exact (spec_sqrt (wn_spec n) y).\n";
  fprintf fmt "  Qed.\n";
  end
  else
   fprintf fmt " Admitted.\n";    
  fprintf fmt "\n";    


  fprintf fmt "End Make.\n";
  fprintf fmt "\n";
  pp_print_flush fmt ()



let _ = print_Make ()


