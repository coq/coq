open Format

let size = 3
let sizeaux = 1

let t = "t"
let c = "N"

(******* Start Printing ********)
let basename = "N"


let print_header fmt l =
  let l = "ZArith"::"Basic_type"::"ZnZ"::"Zn2Z"::"Nbasic"::"GenMul"::
	  "GenDivn1"::"Lucas"::l in
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
  fprintf fmt "    match extend_to_max w%i n m wx wy with\n" size;
  fprintf fmt "    | inl wx' => addn m wx' wy\n";
  fprintf fmt "    | inr wy' => addn n wx wy'\n";
  fprintf fmt "    end\n";
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
  fprintf fmt "  | C1 r => %sn (S n) (WW op.(znz_1) r)" c;
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
  fprintf fmt "    match extend_to_max w%i n m wx wy with\n" size;
  fprintf fmt "    | inl wx' => subn m wx' wy\n";
  fprintf fmt "    | inr wy' => subn n wx wy'\n";
  fprintf fmt "    end\n";
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
  fprintf fmt "    match extend_to_max w%i n m wx wy with\n" size;
  fprintf fmt 
    "    | inl wx' => let op := make_op m in op.(znz_compare) wx' wy \n";
  fprintf fmt 
    "    | inr wy' => let op := make_op n in op.(znz_compare) wx wy' \n";
  fprintf fmt "    end\n";
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
  fprintf fmt "    match extend_to_max w%i n m wx wy with\n" size;
  fprintf fmt "    | inl wx' =>\n";
  fprintf fmt "      let op := make_op m in\n";
  fprintf fmt "      reduce_n (S m) (op.(znz_mul_c) wx' wy)\n";
  fprintf fmt "    | inr wy' =>\n";
  fprintf fmt "      let op := make_op n in\n";
  fprintf fmt "      reduce_n (S n) (op.(znz_mul_c) wx wy')\n";
  fprintf fmt "    end\n";
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
    fprintf fmt "  gen_divn1 w%i_op.(znz_digits) w%i_op.(znz_0)\n" i i;
    fprintf fmt "    w%i_op.(znz_WW) w%i_op.(znz_head0)\n" i i;
    fprintf fmt "    w%i_op.(znz_add_mul_div) w%i_op.(znz_div21).\n" i i
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
  fprintf fmt "    match extend_to_max w%i n m wx wy with\n" size;
  fprintf fmt "    | inl wx' =>\n";
  fprintf fmt "      let (q, r):= (make_op m).(znz_div) wx' wy in\n";
  fprintf fmt "      (reduce_n m q, reduce_n m r)\n";
  fprintf fmt "    | inr wy' =>\n";
  fprintf fmt "      let (q, r):= (make_op n).(znz_div) wx wy' in\n";
  fprintf fmt "      (reduce_n n q, reduce_n n r)\n";
  fprintf fmt "    end\n";
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
    fprintf fmt "  gen_modn1 w%i_op.(znz_digits) w%i_op.(znz_0)\n" i i;
    fprintf fmt 
      "    w%i_op.(znz_head0) w%i_op.(znz_add_mul_div) w%i_op.(znz_div21).\n"
      i i i
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
  fprintf fmt "    match extend_to_max w%i n m wx wy with\n" size;
  fprintf fmt "    | inl wx' =>\n";
  fprintf fmt "      reduce_n m ((make_op m).(znz_mod_gt) wx' wy)\n";
  fprintf fmt "    | inr wy' =>\n";
  fprintf fmt "      reduce_n n ((make_op n).(znz_mod_gt) wx wy')\n";
  fprintf fmt "    end\n";
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

  fprintf fmt " Definition of_pos x :=\n";
  fprintf fmt "  let h := nat_of_P (pheight x) in\n"; 
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


  fprintf fmt "End Make.\n";
  fprintf fmt "\n";
  pp_print_flush fmt ()



let _ = print_Make ()


