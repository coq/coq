open Format

let size = 13
let sizeaux = 1
let gen_proof = false

let t = "t"
let c = "N"
let pz n = if n == 0 then "w_0" else "W0"
let rec gen2 n = if n == 0 then "1" else if n == 1 then "2"
                 else "2 * " ^ (gen2 (n - 1))
let rec genxO n s = 
  if n == 0 then s else " (xO" ^ (genxO (n - 1) s) ^ ")"


(******* Start Printing ********)
let basename = "N"


let print_header fmt l =
  let l = "ZAux"::"ZArith"::"Basic_type"::"ZnZ"::"Zn2Z"::"Nbasic"::"GenMul"::
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

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*        File automatically generated DO NOT EDIT             *)\n";
  fprintf fmt " (*        Constructors: %i  Generated Proofs: %b          %s %s *)\n" size gen_proof (if size < 10 then " " else  "") (if gen_proof then " " else "");
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";


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

  fprintf fmt " Definition to_Z x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx => w%i_op.(znz_to_Z) wx\n" c i i
  done;
  fprintf fmt "  | %sn n wx => (make_op n).(znz_to_Z) wx\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Open Scope Z_scope.\n";
  fprintf fmt " Notation \"[ x ]\" := (to_Z x).\n";
  fprintf fmt " \n";


  if gen_proof then
  begin
  fprintf fmt " (* Regular make op (no karatsuba) *)\n";
  fprintf fmt " Fixpoint nmake_op (ww:Set) (ww_op: znz_op ww) (n: nat) : \n";
  fprintf fmt "       znz_op (word ww n) :=\n";
  fprintf fmt "  match n return znz_op (word ww n) with \n";
  fprintf fmt "   O => ww_op\n";
  fprintf fmt "  | S n1 => mk_zn2z_op (nmake_op ww ww_op n1) \n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
  fprintf fmt " (* Simplification by rewriting for nmake_op *)\n";
  fprintf fmt " Theorem nmake_op_S: forall ww (w_op: znz_op ww) x, \n";
  fprintf fmt "   nmake_op _ w_op (S x) = mk_zn2z_op (nmake_op _ w_op x).\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;


  fprintf fmt " (* Eval and extend functions for each level *)\n";
  for i = 0 to size do
   if gen_proof then
     fprintf fmt " Let nmake_op%i := nmake_op _ w%i_op.\n" i i;
   if gen_proof then
     fprintf fmt " Let eval%in n := znz_to_Z  (nmake_op%i n).\n" i i;
   if i == 0 then 
     fprintf fmt " Let extend%i := GenBase.extend  (WW w_0).\n" i
   else
     fprintf fmt " Let extend%i := GenBase.extend  (WW (W0: w%i)).\n" i i;
  done;
  fprintf fmt "\n";


  if gen_proof then
  begin
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


  fprintf fmt " Theorem digits_nmake:forall n ww (w_op: znz_op ww), \n";
  fprintf fmt "    znz_digits (nmake_op _ w_op (S n)) = \n";
  fprintf fmt "    xO (znz_digits (nmake_op _ w_op n)).\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem znz_nmake_op: forall ww ww_op n xh xl,\n";
  fprintf fmt "  znz_to_Z (nmake_op ww ww_op (S n)) (WW xh xl) =\n";
  fprintf fmt "   znz_to_Z (nmake_op ww ww_op n) xh *\n";
  fprintf fmt "    base (znz_digits (nmake_op ww ww_op n)) +\n";
  fprintf fmt "   znz_to_Z (nmake_op ww ww_op n) xl.\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " auto.\n";
  fprintf fmt " Qed.\n";
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


  for i = 1 to size + 2 do
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

  if gen_proof then
  begin
  fprintf fmt " Let w0_spec: znz_spec w0_op := W0.w_spec.\n";
  for i = 1 to 3 do
    fprintf fmt " Let w%i_spec: znz_spec w%i_op := mk_znz2_spec w%i_spec.\n" i i (i-1) 
  done;
  for i = 4 to size + 3 do
    fprintf fmt " Let w%i_spec : znz_spec w%i_op := mk_znz2_karatsuba_spec w%i_spec.\n" i i (i-1)
  done;
  fprintf fmt "\n";

  fprintf fmt " Let wn_spec: forall n, znz_spec (make_op n).\n";
  fprintf fmt "  intros n; elim n; clear n.\n";
  fprintf fmt "    exact w%i_spec.\n" (size + 1);
  fprintf fmt "  intros n Hrec; rewrite make_op_S.\n";
  fprintf fmt "  exact (mk_znz2_karatsuba_spec Hrec).\n";
  fprintf fmt " Qed.\n";
  fprintf fmt " \n";
  end;

  for i = 0 to size do
    fprintf fmt " Definition w%i_eq0 := w%i_op.(znz_eq0).\n" i i;
    fprintf fmt " Let spec_w%i_eq0: forall x, if w%i_eq0 x then [%s%i x] = 0 else True.\n" i i c i;
    if gen_proof then
    begin
    fprintf fmt " intros x; unfold w%i_eq0, to_Z; generalize (spec_eq0 w%i_spec x);\n" i i;
    fprintf fmt "    case znz_eq0; auto.\n";
    fprintf fmt " Qed.\n";
    end
    else
    fprintf fmt " Admitted.\n";
    fprintf fmt "\n";
  done;
  fprintf fmt "\n";

  
  if gen_proof then
  begin
  for i = 0 to size do
     fprintf fmt " Theorem digits_w%i:  znz_digits w%i_op = znz_digits (nmake_op _ w0_op %i).\n" i i i; 
     if i == 0 then
       fprintf fmt " auto.\n"
     else
       fprintf fmt " rewrite digits_nmake; rewrite <- digits_w%i; auto.\n" (i - 1);
     fprintf fmt " Qed.\n";
     fprintf fmt "\n";

     fprintf fmt " Let spec_gen_eval%in: forall n, eval%in n = GenBase.gen_to_Z (znz_digits w%i_op) (znz_to_Z w%i_op) n.\n" i i i i; 
    if gen_proof then
    begin
     fprintf fmt "  intros n; exact (nmake_gen n w%i w%i_op).\n" i i;
     fprintf fmt " Qed.\n";
    end
    else
    fprintf fmt " Admitted.\n";
    fprintf fmt "\n";
   done;

  for i = 0 to size do
   for j = 0 to (size - i) do
     fprintf fmt " Theorem digits_w%in%i: znz_digits w%i_op = znz_digits (nmake_op _ w%i_op %i).\n" i j (i + j) i j; 
     if j == 0 then
       if i == 0 then
         fprintf fmt " auto.\n"
       else
         begin
           fprintf fmt " apply trans_equal with (xO (znz_digits w%i_op)).\n" (i + j -1);
           fprintf fmt "  auto.\n";
           fprintf fmt "  unfold nmake_op; auto.\n";
         end
     else
     begin
     fprintf fmt " apply trans_equal with (xO (znz_digits w%i_op)).\n" (i + j -1);
     fprintf fmt "  auto.\n";
     fprintf fmt " rewrite digits_nmake.\n";
     fprintf fmt " rewrite digits_w%in%i.\n" i (j - 1);
     fprintf fmt " auto.\n";
     end;
     fprintf fmt " Qed.\n";
     fprintf fmt "\n";
     fprintf fmt " Let spec_eval%in%i: forall x, [%s%i x] = eval%in %i x.\n" i j c (i + j) i j; 
     if gen_proof then
     begin
       if j == 0 then
         fprintf fmt " intros x; rewrite spec_gen_eval%in; unfold GenBase.gen_to_Z, to_Z; auto.\n" i
       else
       begin
        fprintf fmt " intros x; case x.\n";
        fprintf fmt "   auto.\n";
        fprintf fmt " intros xh xl; unfold to_Z; rewrite znz_to_Z_%i.\n" (i + j);
        fprintf fmt " rewrite digits_w%in%i.\n" i (j - 1);
        fprintf fmt " generalize (spec_eval%in%i); unfold to_Z; intros HH; repeat rewrite HH.\n" i (j - 1);
        fprintf fmt " unfold eval%in, nmake_op%i.\n" i i;
        fprintf fmt " rewrite (znz_nmake_op _ w%i_op %i); auto.\n" i (j - 1);

       end;
     fprintf fmt " Qed.\n";
     end
     else
     fprintf fmt " Admitted.\n";
     if i + j <> size  then
       begin
        fprintf fmt " Let spec_extend%in%i: forall x, [%s%i x] = [%s%i (extend%i %i x)].\n" i (i + j + 1) c i c (i + j + 1) i j; 
        if j == 0 then
          begin
           fprintf fmt " intros x; change (extend%i 0 x) with (WW (znz_0 w%i_op) x).\n" i (i + j);
           fprintf fmt " unfold to_Z; rewrite znz_to_Z_%i.\n" (i + j + 1);
           fprintf fmt " rewrite (spec_0 w%i_spec); auto.\n" (i + j);

          end
        else
          begin
           fprintf fmt " intros x; change (extend%i %i x) with (WW (znz_0 w%i_op) (extend%i %i x)).\n" i j (i + j) i (j - 1);
          fprintf fmt " unfold to_Z; rewrite znz_to_Z_%i.\n" (i + j + 1);
          fprintf fmt " rewrite (spec_0 w%i_spec).\n" (i + j);
          fprintf fmt " generalize (spec_extend%in%i x); unfold to_Z.\n" i (i + j);
          fprintf fmt " intros HH; rewrite <- HH; auto.\n";

          end;
          fprintf fmt " Qed.\n";
          fprintf fmt "\n";
       end;
   done;

   fprintf fmt " Theorem digits_w%in%i: znz_digits w%i_op = znz_digits (nmake_op _ w%i_op %i).\n" i (size - i + 1) (size + 1) i (size - i + 1);
   fprintf fmt " apply trans_equal with (xO (znz_digits w%i_op)).\n" size;
   fprintf fmt "  auto.\n";
   fprintf fmt " rewrite digits_nmake.\n";
   fprintf fmt " rewrite digits_w%in%i.\n" i (size - i);
   fprintf fmt " auto.\n";
   fprintf fmt " Qed.\n";
   fprintf fmt "\n";

   fprintf fmt " Let spec_eval%in%i: forall x, [%sn 0  x] = eval%in %i x.\n" i (size - i + 1) c i (size - i + 1); 
   fprintf fmt " intros x; case x.\n";
   fprintf fmt "   auto.\n";
   fprintf fmt " intros xh xl; unfold to_Z; rewrite znz_to_Z_%i.\n" (size + 1);
   fprintf fmt " rewrite digits_w%in%i.\n" i (size - i);
   fprintf fmt " generalize (spec_eval%in%i); unfold to_Z; intros HH; repeat rewrite HH.\n" i (size - i);
   fprintf fmt " unfold eval%in, nmake_op%i.\n" i i;
   fprintf fmt " rewrite (znz_nmake_op _ w%i_op %i); auto.\n" i (size - i);
   fprintf fmt " Qed.\n";
   fprintf fmt "\n";

   fprintf fmt " Let spec_eval%in%i: forall x, [%sn 1  x] = eval%in %i x.\n" i (size - i + 2) c i (size - i + 2); 
   fprintf fmt " intros x; case x.\n";
   fprintf fmt "   auto.\n";
   fprintf fmt " intros xh xl; unfold to_Z; rewrite znz_to_Z_%i.\n" (size + 2);
   fprintf fmt " rewrite digits_w%in%i.\n" i (size + 1 - i);
   fprintf fmt " generalize (spec_eval%in%i); unfold to_Z; change (make_op 0) with (w%i_op); intros HH; repeat rewrite HH.\n" i (size + 1 - i) (size + 1);
   fprintf fmt " unfold eval%in, nmake_op%i.\n" i i;
   fprintf fmt " rewrite (znz_nmake_op _ w%i_op %i); auto.\n" i (size + 1 - i);
   fprintf fmt " Qed.\n";
   fprintf fmt "\n";
  done;

  fprintf fmt " Let digits_w%in: forall n,\n" size;
  fprintf fmt "   znz_digits (make_op n) = znz_digits (nmake_op _ w%i_op (S n)).\n" size;
  fprintf fmt " intros n; elim n; clear n.\n";
  fprintf fmt "  change (znz_digits (make_op 0)) with (xO (znz_digits w%i_op)).\n" size;
  fprintf fmt "  rewrite nmake_op_S; apply sym_equal; auto.\n";
  fprintf fmt "  intros  n Hrec.\n";
  fprintf fmt "  replace (znz_digits (make_op (S n))) with (xO (znz_digits (make_op n))).\n";
  fprintf fmt "  rewrite Hrec.\n";
  fprintf fmt "  rewrite nmake_op_S; apply sym_equal; auto.\n";
  fprintf fmt "  rewrite make_op_S; apply sym_equal; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";

  fprintf fmt " Let spec_eval%in: forall n x, [%sn n x] = eval%in (S n) x.\n" size c size; 
  fprintf fmt " intros n; elim n; clear n.\n";
  fprintf fmt "   exact spec_eval%in1.\n" size;
  fprintf fmt " intros n Hrec x; case x; clear x.\n";
  fprintf fmt "  unfold to_Z, eval%in, nmake_op%i.\n" size size;
  fprintf fmt "    rewrite make_op_S; rewrite nmake_op_S; auto.\n";
  fprintf fmt " intros xh xl.\n";
  fprintf fmt "  unfold to_Z in Hrec |- *.\n";
  fprintf fmt "  rewrite znz_to_Z_n.\n";
  fprintf fmt "  rewrite digits_w%in.\n" size;
  fprintf fmt "  repeat rewrite Hrec.\n";
  fprintf fmt "  unfold eval%in, nmake_op%i.\n" size size;
  fprintf fmt "  apply sym_equal; rewrite nmake_op_S; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";

  fprintf fmt " Let spec_extend%in: forall n x, [%s%i x] = [%sn n (extend%i n x)].\n" size c size c size ; 
  fprintf fmt " intros n; elim n; clear n.\n";
  fprintf fmt "   intros x; change (extend%i 0 x) with (WW (znz_0 w%i_op) x).\n" size size;
  fprintf fmt "   unfold to_Z.\n";
  fprintf fmt "   change (make_op 0) with w%i_op.\n" (size + 1);
  fprintf fmt "   rewrite znz_to_Z_%i; rewrite (spec_0 w%i_spec); auto.\n" (size + 1) size;
  fprintf fmt " intros n Hrec x.\n";
  fprintf fmt "   change (extend%i (S n) x) with (WW W0 (extend%i n x)).\n" size size;
  fprintf fmt "   unfold to_Z in Hrec |- *; rewrite znz_to_Z_n; auto.\n";
  fprintf fmt "   rewrite <- Hrec.\n";
  fprintf fmt "  replace (znz_to_Z (make_op n) W0) with 0; auto.\n";
  fprintf fmt "  case n; auto; intros; rewrite make_op_S; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;



  fprintf fmt " Theorem to_Z_pos: forall x, 0 <= [x].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; clear x.\n";
  for i = 0 to size do
    fprintf fmt " intros x; case (spec_to_Z w%i_spec x); auto.\n" i;
  done;
  fprintf fmt " intros n x; case (spec_to_Z (wn_spec n) x); auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  if gen_proof then
  begin
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
  end;


  fprintf fmt " Section LevelAndIter.\n";
  fprintf fmt "\n";
  fprintf fmt "  Variable res: Set.\n";
  fprintf fmt "  Variable xxx: res.\n";
  fprintf fmt "  Variable P: Z -> Z -> res -> Prop.\n";
  fprintf fmt "  (* Abstraction function for each level *)\n";
  for i = 0 to size do
   fprintf fmt "  Variable f%i: w%i -> w%i -> res.\n" i i i;
   fprintf fmt "  Variable f%in: forall n, w%i -> word w%i (S n) -> res.\n" i i i;
   fprintf fmt "  Variable fn%i: forall n, word w%i (S n) -> w%i -> res.\n" i i i;
   if gen_proof then
   begin
   fprintf fmt "  Variable Pf%i: forall x y, P [%s%i x] [%s%i y] (f%i x y).\n" i c i c i i;
   if i == size then
     begin
      fprintf fmt "  Variable Pf%in: forall n x y, P [%s%i x] (eval%in (S n) y) (f%in n x y).\n" i c i i i;
      fprintf fmt "  Variable Pfn%i: forall n x y, P (eval%in (S n) x) [%s%i y] (fn%i n x y).\n" i i c i i;
     end
   else
     begin

   fprintf fmt "  Variable Pf%in: forall n x y, Z_of_nat n <= %i -> P [%s%i x] (eval%in (S n) y) (f%in n x y).\n" i (size - i) c i i i;
   fprintf fmt "  Variable Pfn%i: forall n x y, Z_of_nat n <= %i -> P (eval%in (S n) x) [%s%i y] (fn%i n x y).\n" i (size - i) i c i i;
     end;
   end;
   fprintf fmt "\n";
  done;
  fprintf fmt "  Variable fnn: forall n, word w%i (S n) -> word w%i (S n) -> res.\n" size size;
  if gen_proof then
    fprintf fmt "  Variable Pfnn: forall n x y, P [%sn n x] [%sn n y] (fnn n x y).\n" c c;
  fprintf fmt "  Variable fnm: forall n m, word w%i (S n) -> word w%i (S m) -> res.\n" size size;
  if gen_proof then 
    fprintf fmt "  Variable Pfnm: forall n m x y, P [%sn n x] [%sn m y] (fnm n m x y).\n" c c;
  fprintf fmt "\n";
  fprintf fmt "  (* Special zero functions *)\n";
  fprintf fmt "  Variable f0t:  t_ -> res.\n";
  if gen_proof then
    fprintf fmt "  Variable Pf0t: forall x, P 0 [x] (f0t x).\n";
  fprintf fmt "  Variable ft0:  t_ -> res.\n";
  if gen_proof then
    fprintf fmt "  Variable Pft0: forall x, P [x] 0 (ft0 x).\n";
  fprintf fmt "\n";


  fprintf fmt "  (* We level the two arguments before applying *)\n";
  fprintf fmt "  (* the functions at each leval                *)\n";
  fprintf fmt "  Definition same_level (x y: t_): res :=\n";
  fprintf fmt "    Eval lazy zeta beta iota delta [";
  for i = 0 to size do
    fprintf fmt "extend%i " i;
  done;
  fprintf fmt "\n";
  fprintf fmt "                                         GenBase.extend GenBase.extend_aux\n";
  fprintf fmt "                                         ] in\n";
  fprintf fmt "  match x, y with\n";
  for i = 0 to size do
    for j = 0 to i - 1 do
      fprintf fmt "  | %s%i wx, %s%i wy => f%i wx (extend%i %i wy)\n" c i c j i j (i - j -1);
    done;
    fprintf fmt "  | %s%i wx, %s%i wy => f%i wx wy\n" c i c i i;
    for j = i + 1 to size do
      fprintf fmt "  | %s%i wx, %s%i wy => f%i (extend%i %i wx) wy\n" c i c j j i (j - i - 1);
    done;
    if i == size then
      fprintf fmt "  | %s%i wx, %sn m wy => fnn m (extend%i m wx) wy\n" c size c size 
    else 
      fprintf fmt "  | %s%i wx, %sn m wy => fnn m (extend%i m (extend%i %i wx)) wy\n" c i c size i (size - i - 1);
  done;
  for i = 0 to size do
    if i == size then
      fprintf fmt "  | %sn n wx, %s%i wy => fnn n wx (extend%i n wy)\n" c c size size 
    else 
      fprintf fmt "  | %sn n wx, %s%i wy => fnn n wx (extend%i n (extend%i %i wy))\n" c c i size i (size - i - 1);
  done;
  fprintf fmt "  | %sn n wx, Nn m wy =>\n" c;
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "     fnn mn\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d)))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
  if gen_proof then
  begin
  fprintf fmt "  Lemma spec_same_level: forall x y, P [x] [y] (same_level x y).\n";
  fprintf fmt "  Proof.\n";
  fprintf fmt "  intros x; case x; clear x; unfold same_level.\n";
  for i = 0 to size do
    fprintf fmt "    intros x y; case y; clear y.\n";
    for j = 0 to i - 1 do
      fprintf fmt "     intros y; rewrite spec_extend%in%i; apply Pf%i.\n" j i i;
    done;
    fprintf fmt "     intros y; apply Pf%i.\n" i;
    for j = i + 1 to size do
      fprintf fmt "     intros y; rewrite spec_extend%in%i; apply Pf%i.\n" i j j;
    done;
    if i == size then
      fprintf fmt "     intros m y; rewrite (spec_extend%in m); apply Pfnn.\n" size
    else 
      fprintf fmt "     intros m y; rewrite spec_extend%in%i; rewrite (spec_extend%in m); apply Pfnn.\n" i size size;
  done;
  fprintf fmt "    intros n x y; case y; clear y.\n";
  for i = 0 to size do
    if i == size then
      fprintf fmt "    intros y; rewrite (spec_extend%in n); apply Pfnn.\n" size
    else 
      fprintf fmt "    intros y; rewrite spec_extend%in%i; rewrite (spec_extend%in n); apply Pfnn.\n" i size size;
  done;
  fprintf fmt "    intros m y; rewrite <- (spec_cast_l n m x); \n";
  fprintf fmt "          rewrite <- (spec_cast_r n m y); apply Pfnn.\n";
  fprintf fmt "  Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt "  (* We level the two arguments before applying      *)\n";
  fprintf fmt "  (* the functions at each level (special zero case) *)\n";
  fprintf fmt "  Definition same_level0 (x y: t_): res :=\n";
  fprintf fmt "    Eval lazy zeta beta iota delta [";
  for i = 0 to size do
    fprintf fmt "extend%i " i;
  done;
  fprintf fmt "\n";
  fprintf fmt "                                         GenBase.extend GenBase.extend_aux\n";
  fprintf fmt "                                         ] in\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx =>\n" c i;
    if (i == 0) then
      fprintf fmt "    if w0_eq0 wx then f0t y else\n";
    fprintf fmt "    match y with\n";
    for j = 0 to i - 1 do
      fprintf fmt "    | %s%i wy =>\n" c j;
      if j == 0 then 
        fprintf fmt "       if w0_eq0 wy then ft0 x else\n";
      fprintf fmt "       f%i wx (extend%i %i wy)\n" i j (i - j -1);
    done;
    fprintf fmt "    | %s%i wy => f%i wx wy\n" c i i;
    for j = i + 1 to size do
      fprintf fmt "    | %s%i wy => f%i (extend%i %i wx) wy\n" c j j i (j - i - 1);
    done;
    if i == size then
      fprintf fmt "    | %sn m wy => fnn m (extend%i m wx) wy\n" c size 
    else 
      fprintf fmt "    | %sn m wy => fnn m (extend%i m (extend%i %i wx)) wy\n" c size i (size - i - 1);
    fprintf fmt"    end\n";
  done;
  fprintf fmt "  |  %sn n wx =>\n" c;
  fprintf fmt "     match y with\n";
  for i = 0 to size do
    fprintf fmt "     | %s%i wy =>\n" c i;
    if i == 0 then
      fprintf fmt "      if w0_eq0 wy then ft0 x else\n";
    if i == size then
      fprintf fmt "      fnn n wx (extend%i n wy)\n" size 
    else 
      fprintf fmt "      fnn n wx (extend%i n (extend%i %i wy))\n" size i (size - i - 1);
  done;
  fprintf fmt "        | %sn m wy =>\n" c;
  fprintf fmt "            let mn := Max.max n m in\n";
  fprintf fmt "            let d := diff n m in\n";
  fprintf fmt "              fnn mn\n";
  fprintf fmt "              (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "              (castm (diff_l n m) (extend_tr wy (fst d)))\n";
  fprintf fmt "    end\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  if gen_proof then
  begin
  fprintf fmt "  Lemma spec_same_level0: forall x y, P [x] [y] (same_level0 x y).\n";
  fprintf fmt "  Proof.\n";
  fprintf fmt "  intros x; case x; clear x; unfold same_level0.\n";
  for i = 0 to size do
    fprintf fmt "    intros x.\n";
    if i == 0 then
      begin
        fprintf fmt "    generalize (spec_w0_eq0 x); case w0_eq0; intros H.\n";
        fprintf fmt "      intros y; rewrite H; apply Pf0t.\n";
        fprintf fmt "    clear H.\n";
      end;
    fprintf fmt "    intros y; case y; clear y.\n";
    for j = 0 to i - 1 do
      fprintf fmt "     intros y.\n";
      if j == 0 then
        begin
          fprintf fmt "     generalize (spec_w0_eq0 y); case w0_eq0; intros H.\n";
          fprintf fmt "       rewrite H; apply Pft0.\n";
          fprintf fmt "     clear H.\n";
        end;
      fprintf fmt "     rewrite spec_extend%in%i; apply Pf%i.\n" j i i;
    done;
    fprintf fmt "     intros y; apply Pf%i.\n" i;
    for j = i + 1 to size do
      fprintf fmt "     intros y; rewrite spec_extend%in%i; apply Pf%i.\n" i j j;
    done;
    if i == size then
      fprintf fmt "     intros m y; rewrite (spec_extend%in m); apply Pfnn.\n" size
    else 
      fprintf fmt "     intros m y; rewrite spec_extend%in%i; rewrite (spec_extend%in m); apply Pfnn.\n" i size size;
  done;
  fprintf fmt "    intros n x y; case y; clear y.\n";
  for i = 0 to size do
    fprintf fmt "    intros y.\n";
    if i = 0 then
        begin
          fprintf fmt "     generalize (spec_w0_eq0 y); case w0_eq0; intros H.\n";
          fprintf fmt "       rewrite H; apply Pft0.\n";
          fprintf fmt "     clear H.\n";
        end;
    if i == size then
      fprintf fmt "    rewrite (spec_extend%in n); apply Pfnn.\n" size
    else 
      fprintf fmt "    rewrite spec_extend%in%i; rewrite (spec_extend%in n); apply Pfnn.\n" i size size;
  done;
  fprintf fmt "  intros m y; rewrite <- (spec_cast_l n m x); \n";
  fprintf fmt "          rewrite <- (spec_cast_r n m y); apply Pfnn.\n";
  fprintf fmt "  Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt "  (* We iter the smaller argument with the bigger  *)\n";
  fprintf fmt "  Definition iter (x y: t_): res := \n";
  fprintf fmt "    Eval lazy zeta beta iota delta [";
  for i = 0 to size do
    fprintf fmt "extend%i " i;
  done;
  fprintf fmt "\n";
  fprintf fmt "                                         GenBase.extend GenBase.extend_aux\n";
  fprintf fmt "                                         ] in\n";
  fprintf fmt "  match x, y with\n";
  for i = 0 to size do
    for j = 0 to i - 1 do
      fprintf fmt "  | %s%i wx, %s%i wy => fn%i %i wx wy\n" c i c j j (i - j - 1);
    done;
    fprintf fmt "  | %s%i wx, %s%i wy => f%i wx wy\n" c i c i i;
    for j = i + 1 to size do
      fprintf fmt "  | %s%i wx, %s%i wy => f%in %i wx wy\n" c i c j i (j - i - 1);
    done;
    if i == size then
      fprintf fmt "  | %s%i wx, %sn m wy => f%in m wx wy\n" c size c size 
    else 
      fprintf fmt "  | %s%i wx, %sn m wy => f%in m (extend%i %i wx) wy\n" c i c size i (size - i - 1);
  done;
  for i = 0 to size do
    if i == size then
      fprintf fmt "  | %sn n wx, %s%i wy => fn%i n wx wy\n" c c size size 
    else 
      fprintf fmt "  | %sn n wx, %s%i wy => fn%i n wx (extend%i %i wy)\n" c c i size i (size - i - 1);
  done;
  fprintf fmt "  | %sn n wx, %sn m wy => fnm n m wx wy\n" c c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  if gen_proof then
  begin
  fprintf fmt "  Ltac zg_tac := try\n";
  fprintf fmt "    (red; simpl Zcompare; auto;\n";
  fprintf fmt "     let t := fresh \"H\" in (intros t; discriminate H)).\n";
  fprintf fmt "  Lemma spec_iter: forall x y, P [x] [y] (iter x y).\n";
  fprintf fmt "  Proof.\n";
  fprintf fmt "  intros x; case x; clear x; unfold iter.\n";
  for i = 0 to size do
    fprintf fmt "    intros x y; case y; clear y.\n";
    for j = 0 to i - 1 do
      fprintf fmt "     intros y; rewrite spec_eval%in%i;  apply (Pfn%i %i); zg_tac.\n" j (i - j) j (i - j - 1);
    done;
    fprintf fmt "     intros y; apply Pf%i.\n" i;
    for j = i + 1 to size do
      fprintf fmt "     intros y; rewrite spec_eval%in%i; apply (Pf%in %i); zg_tac.\n" i (j - i) i (j - i - 1);
    done;
    if i == size then
        fprintf fmt "     intros m y; rewrite spec_eval%in; apply Pf%in.\n" size size
    else 
        fprintf fmt "     intros m y; rewrite spec_extend%in%i; rewrite spec_eval%in; apply Pf%in.\n" i size size size;
  done;
  fprintf fmt "    intros n x y; case y; clear y.\n";
  for i = 0 to size do
    if i == size then
      fprintf fmt "     intros y; rewrite spec_eval%in; apply Pfn%i.\n" size size
    else 
     fprintf fmt "      intros y; rewrite spec_extend%in%i; rewrite spec_eval%in; apply Pfn%i.\n" i size size size;
  done;
  fprintf fmt "  intros m y; apply Pfnm.\n";
  fprintf fmt "  Qed.\n";
  fprintf fmt "\n";
  end;


  fprintf fmt "  (* We iter the smaller argument with the bigger  (zero case) *)\n";
  fprintf fmt "  Definition iter0 (x y: t_): res :=\n";
  fprintf fmt "    Eval lazy zeta beta iota delta [";
  for i = 0 to size do
    fprintf fmt "extend%i " i;
  done;
  fprintf fmt "\n";
  fprintf fmt "                                         GenBase.extend GenBase.extend_aux\n";
  fprintf fmt "                                         ] in\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx =>\n" c i;
    if (i == 0) then
      fprintf fmt "    if w0_eq0 wx then f0t y else\n";
    fprintf fmt "    match y with\n";
    for j = 0 to i - 1 do
      fprintf fmt "    | %s%i wy =>\n" c j;
      if j == 0 then
        fprintf fmt "       if w0_eq0 wy then ft0 x else\n";
      fprintf fmt "       fn%i %i wx wy\n" j (i - j - 1);
    done;
    fprintf fmt "    | %s%i wy => f%i wx wy\n" c i i;
    for j = i + 1 to size do
      fprintf fmt "    | %s%i wy => f%in %i wx wy\n" c j i (j - i - 1);
    done;
    if i == size then
      fprintf fmt "    | %sn m wy => f%in m wx wy\n" c size 
    else 
      fprintf fmt "    | %sn m wy => f%in m (extend%i %i wx) wy\n" c size i (size - i - 1);
    fprintf fmt "    end\n";
  done;
  fprintf fmt "  | %sn n wx =>\n" c;
  fprintf fmt "    match y with\n";
  for i = 0 to size do
    fprintf fmt "    | %s%i wy =>\n" c i;
    if i == 0 then
      fprintf fmt "      if w0_eq0 wy then ft0 x else\n";
    if i == size then
      fprintf fmt "      fn%i n wx wy\n" size 
    else 
      fprintf fmt "      fn%i n wx (extend%i %i wy)\n" size i (size - i - 1);
  done;
  fprintf fmt "    | %sn m wy => fnm n m wx wy\n" c;
  fprintf fmt "    end\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  if gen_proof then
  begin
  fprintf fmt "  Lemma spec_iter0: forall x y, P [x] [y] (iter0 x y).\n";
  fprintf fmt "  Proof.\n";
  fprintf fmt "  intros x; case x; clear x; unfold iter0.\n";
  for i = 0 to size do
    fprintf fmt "    intros x.\n";
    if i == 0 then
      begin
        fprintf fmt "    generalize (spec_w0_eq0 x); case w0_eq0; intros H.\n";
        fprintf fmt "      intros y; rewrite H; apply Pf0t.\n";
        fprintf fmt "    clear H.\n";
      end;
    fprintf fmt "    intros y; case y; clear y.\n";
    for j = 0 to i - 1 do
      fprintf fmt "     intros y.\n";
      if j == 0 then
        begin
          fprintf fmt "     generalize (spec_w0_eq0 y); case w0_eq0; intros H.\n";
          fprintf fmt "       rewrite H; apply Pft0.\n";
          fprintf fmt "     clear H.\n";
        end;
      fprintf fmt "     rewrite spec_eval%in%i;  apply (Pfn%i %i); zg_tac.\n" j (i - j) j (i - j - 1);
    done;
    fprintf fmt "     intros y; apply Pf%i.\n" i;
    for j = i + 1 to size do
      fprintf fmt "     intros y; rewrite spec_eval%in%i; apply (Pf%in %i); zg_tac.\n" i (j - i) i (j - i - 1);
    done;
    if i == size then
        fprintf fmt "     intros m y; rewrite spec_eval%in; apply Pf%in.\n" size size
    else 
        fprintf fmt "     intros m y; rewrite spec_extend%in%i; rewrite spec_eval%in; apply Pf%in.\n" i size size size;
  done;
  fprintf fmt "    intros n x y; case y; clear y.\n";
  for i = 0 to size do
    fprintf fmt "    intros y.\n";
    if i = 0 then
        begin
          fprintf fmt "     generalize (spec_w0_eq0 y); case w0_eq0; intros H.\n";
          fprintf fmt "       rewrite H; apply Pft0.\n";
          fprintf fmt "     clear H.\n";
        end;
    if i == size then
      fprintf fmt "     rewrite spec_eval%in; apply Pfn%i.\n" size size
    else 
     fprintf fmt "      rewrite spec_extend%in%i; rewrite spec_eval%in; apply Pfn%i.\n" i size size size;
  done;
  fprintf fmt "  intros m y; apply Pfnm.\n";
  fprintf fmt "  Qed.\n";
  fprintf fmt "\n";
  end;


  fprintf fmt "  End LevelAndIter.\n";
  fprintf fmt "\n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Reduction                         *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

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

  if gen_proof then 
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
  end;

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Successor                         *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

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

  fprintf fmt " Theorem succ_spec: forall n, [succ n] = [n] + 1.\n";
  if gen_proof then
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
  fprintf fmt " Qed.\n";
  end
  else fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Adddition                         *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";
  for i = 0 to size do
    fprintf fmt " Definition w%i_add_c := znz_add_c w%i_op.\n" i i; 
    fprintf fmt " Definition w%i_add x y :=\n" i;
    fprintf fmt "  match w%i_add_c x y with\n" i;
    fprintf fmt "  | C0 r => %s%i r\n" c i;
    if i == size then
      fprintf fmt "  | C1 r => %sn 0 (WW one%i r)\n" c size
    else
      fprintf fmt "  | C1 r => %s%i (WW one%i r)\n" c (i + 1) i;
    fprintf fmt "  end.\n";
    fprintf fmt "\n";
  done ;
  fprintf fmt " Definition addn n (x y : word w%i (S n)) :=\n" size;
  fprintf fmt "  let op := make_op n in\n";
  fprintf fmt "  match op.(znz_add_c) x y with\n";
  fprintf fmt "  | C0 r => %sn n r\n" c;
  fprintf fmt "  | C1 r => %sn (S n) (WW op.(znz_1) r)  end.\n" c;
  fprintf fmt "\n";


  if gen_proof then 
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
  end;

  fprintf fmt " Definition add := Eval lazy beta delta [same_level] in\n";
  fprintf fmt "   (same_level t_ ";
  for i = 0 to size do
    fprintf fmt "w%i_add " i;
  done;
  fprintf fmt "addn).\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_add: forall x y, [add x y] = [x] + [y].\n";
  if gen_proof then
  begin 
  fprintf fmt " Proof.\n";
  fprintf fmt " unfold add.\n";
  fprintf fmt " generalize (spec_same_level t_ (fun x y res => [res] = x + y)).\n";
  fprintf fmt " unfold same_level; intros HH; apply HH; clear HH.\n";
  for i = 0 to size do
    fprintf fmt " exact spec_w%i_add.\n" i;
  done;
  fprintf fmt " exact spec_wn_add.\n";
  fprintf fmt " Qed.\n";
  end 
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Predecessor                       *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

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

  fprintf fmt " Let spec_pred: forall x, 0 < [x] -> [pred x] = [x] - 1.\n";
  if gen_proof then
  begin
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
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt " \n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Subtraction                       *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

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

  if gen_proof then
  begin
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

  fprintf fmt " Definition sub := Eval lazy beta delta [same_level] in\n";
  fprintf fmt "   (same_level t_ ";
  for i = 0 to size do
    fprintf fmt "w%i_sub " i;
  done;
  fprintf fmt "subn).\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_sub: forall x y, [y] <= [x] -> [sub x y] = [x] - [y].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " unfold sub.\n";
  fprintf fmt " generalize (spec_same_level t_ (fun x y res => y <= x -> [res] = x - y)).\n";
  fprintf fmt " unfold same_level; intros HH; apply HH; clear HH.\n";
  for i = 0 to size do
    fprintf fmt " exact spec_w%i_sub.\n" i;
  done;
  fprintf fmt " exact spec_wn_sub.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  if gen_proof then
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
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " unfold sub.\n";
  fprintf fmt " generalize (spec_same_level t_ (fun x y res => x < y -> [res] = 0)).\n";
  fprintf fmt " unfold same_level; intros HH; apply HH; clear HH.\n";
  for i = 0 to size do
    fprintf fmt " exact spec_w%i_sub0.\n" i;
  done;
  fprintf fmt " exact spec_wn_sub0.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Comparison                        *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

  for i = 0 to size do
    fprintf fmt " Definition compare_%i := w%i_op.(znz_compare).\n" i i;
    fprintf fmt " Definition comparen_%i :=\n" i;
    let s0 = if i = 0 then "w_0" else "W0" in
    fprintf fmt 
      "  compare_mn_1 w%i w%i %s compare_%i (compare_%i %s) compare_%i.\n" 
                        i   i  s0         i           i  s0          i
  done;
  fprintf fmt "\n"; 

  fprintf fmt " Definition comparenm n m wx wy :=\n";
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "     op.(znz_compare)\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr wy (fst d))).\n";
  fprintf fmt "\n";

  fprintf fmt " Definition compare := Eval lazy beta delta [iter] in \n";
  fprintf fmt "   (iter _ \n";
  for i = 0 to size do
    fprintf fmt "      compare_%i\n" i;
    fprintf fmt "      (fun n x y => opp_compare (comparen_%i (S n) y x))\n" i;
    fprintf fmt "      (fun n => comparen_%i (S n))\n" i;
  done;
  fprintf fmt "      comparenm).\n";
  fprintf fmt "\n";

  if gen_proof then
  begin
  for i = 0 to size do
    fprintf fmt " Let spec_compare_%i: forall x y,\n" i;
    fprintf fmt "    match compare_%i x y with \n" i;
    fprintf fmt "      Eq => [%s%i x] = [%s%i y]\n" c i c i;
    fprintf fmt "    | Lt => [%s%i x] < [%s%i y]\n" c i c i;
    fprintf fmt "    | Gt => [%s%i x] > [%s%i y]\n" c i c i;
    fprintf fmt "    end.\n";
    fprintf fmt "  Proof.\n";
    fprintf fmt "  unfold compare_%i, to_Z; exact (spec_compare w%i_spec).\n" i i;
    fprintf fmt "  Qed.\n";
    fprintf fmt "\n";

    fprintf fmt "  Let spec_comparen_%i:\n" i;
    fprintf fmt "  forall (n : nat) (x : word w%i n) (y : w%i),\n" i i;
    fprintf fmt "  match comparen_%i n x y with\n" i;
    fprintf fmt "  | Eq => eval%in n x = [%s%i y]\n" i c i;
    fprintf fmt "  | Lt => eval%in n x < [%s%i y]\n" i c i;
    fprintf fmt "  | Gt => eval%in n x > [%s%i y]\n" i c i;
    fprintf fmt "  end.\n";
    fprintf fmt "  intros n x y.\n";
    fprintf fmt "  unfold comparen_%i, to_Z; rewrite spec_gen_eval%in.\n" i i;
    fprintf fmt "  apply spec_compare_mn_1.\n";
    fprintf fmt "  exact (spec_0 w%i_spec).\n" i;
    if i == 0 then
      fprintf fmt "  intros x1; exact (spec_compare w%i_spec w_0 x1).\n" i
    else
      fprintf fmt "  intros x1; exact (spec_compare w%i_spec W0 x1).\n" i;
    fprintf fmt "  exact (spec_to_Z w%i_spec).\n" i;
    fprintf fmt "  exact (spec_compare w%i_spec).\n" i;
    fprintf fmt "  exact (spec_compare w%i_spec).\n" i;
    fprintf fmt "  exact (spec_to_Z w%i_spec).\n" i;
    fprintf fmt "  Qed.\n";
    fprintf fmt "\n";

  done;

  fprintf fmt " Let spec_opp_compare: forall c (u v: Z),\n";
  fprintf fmt "  match c with Eq => u = v | Lt => u < v | Gt => u > v end ->\n";
  fprintf fmt "  match opp_compare c with Eq => v = u | Lt => v < u | Gt => v > u end.\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros c u v; case c; unfold opp_compare; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Theorem spec_compare: forall x y,\n";
  fprintf fmt "    match compare x y with \n";
  fprintf fmt "      Eq => [x] = [y]\n";
  fprintf fmt "    | Lt => [x] < [y]\n";
  fprintf fmt "    | Gt => [x] > [y]\n";
  fprintf fmt "    end.\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " refine (spec_iter _ (fun x y res => \n";
  fprintf fmt "                       match res with \n";
  fprintf fmt "                        Eq => x = y\n";
  fprintf fmt "                      | Lt => x < y\n";
  fprintf fmt "                      | Gt => x > y\n";
  fprintf fmt "                      end)\n";
  for i = 0 to size do
    fprintf fmt "      compare_%i\n" i;
    fprintf fmt "      (fun n x y => opp_compare (comparen_%i (S n) y x))\n" i;
    fprintf fmt "      (fun n => comparen_%i (S n)) _ _ _\n" i;
  done;
  fprintf fmt "      comparenm _).\n";

  for i = 0 to size - 1 do
  fprintf fmt "  exact spec_compare_%i.\n" i;
  fprintf fmt "  intros n x y H;apply spec_opp_compare; apply spec_comparen_%i.\n" i;
  fprintf fmt "  intros n x y H; exact (spec_comparen_%i (S n) x y).\n" i;
  done; 
  fprintf fmt "  exact spec_compare_%i.\n" size;
  fprintf fmt "  intros n x y;apply spec_opp_compare; apply spec_comparen_%i.\n" size;
  fprintf fmt "  intros n; exact (spec_comparen_%i (S n)).\n" size;
  fprintf fmt "  intros n m x y; unfold comparenm.\n";
  fprintf fmt "  rewrite <- (spec_cast_l n m x); rewrite <- (spec_cast_r n m y).\n";
  fprintf fmt "  unfold to_Z; apply (spec_compare  (wn_spec (Max.max n m))).\n";
  fprintf fmt "  Qed.\n";
  end 
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition eq_bool x y :=\n";
  fprintf fmt "  match compare x y with\n";
  fprintf fmt "  | Eq => true\n";
  fprintf fmt "  | _  => false\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_eq_bool: forall x y,\n";
  fprintf fmt "    if eq_bool x y then [x] = [y] else [x] <> [y].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x y; unfold eq_bool.\n";
  fprintf fmt " generalize (spec_compare x y); case compare; auto with zarith.\n";
  fprintf fmt "  Qed.\n";
  end 
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";



  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Multiplication                    *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";
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
    fprintf fmt " Definition w%i_0W := w%i_op.(znz_0W).\n" i i
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

  begin
  for i = 0 to size - 1 do
    fprintf fmt "  Let to_Z%i n :=\n" i;
    fprintf fmt "  match n return word w%i (S n) -> t_ with\n" i;
    for j = 0 to size - i do
      if (i + j) == size then
        begin 
          fprintf fmt "  | %i%s => fun x => %sn 0 x\n" j "%nat" c;
          fprintf fmt "  | %i%s => fun x => %sn 1 x\n" (j + 1) "%nat" c
        end
      else
        fprintf fmt "  | %i%s => fun x => %s%i x\n" j "%nat" c (i + j + 1)
    done;
    fprintf fmt   "  | _   => fun _ => N0 w_0\n";
    fprintf fmt "  end.\n";
    fprintf fmt "\n";
  done; 


  if gen_proof then
  for i = 0 to size - 1 do
    fprintf fmt "Theorem to_Z%i_spec:\n" i;
    fprintf fmt "  forall n x, Z_of_nat n <= %i -> [to_Z%i n x] = znz_to_Z (nmake_op _ w%i_op (S n)) x.\n" (size + 1 - i) i i;
    for j = 1 to size + 2 - i do
      fprintf fmt " intros n; case n; clear n.\n";
      fprintf fmt "   unfold to_Z%i.\n" i;
      fprintf fmt "   intros x H; rewrite spec_eval%in%i; auto.\n" i j;
    done;
    fprintf fmt " intros n x.\n";
    fprintf fmt " repeat rewrite inj_S; unfold Zsucc; auto with zarith.\n";
    fprintf fmt " Qed.\n";
    fprintf fmt "\n";
  done; 
  end;

  for i = 0 to size do
    fprintf fmt " Definition w%i_mul n x y :=\n" i;
    if i == 0 then
      fprintf fmt " let (w,r) := w%i_mul_add_n1 (S n) x y w_0 in\n" i
    else
      fprintf fmt " let (w,r) := w%i_mul_add_n1 (S n) x y W0 in\n" i;
    if i == size then
      begin
        fprintf fmt " if w%i_eq0 w then %sn n r\n" i c;
        fprintf fmt " else %sn (S n) (WW (extend%i n w) r).\n" c i;
      end
    else 
      begin 
        fprintf fmt " if w%i_eq0 w then to_Z%i n r\n" i i;
        fprintf fmt " else to_Z%i (S n) (WW (extend%i n w) r).\n" i i;
      end;
    fprintf fmt "\n";
  done;

  fprintf fmt " Definition mulnm n m x y :=\n";
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "     reduce_n (S mn) (op.(znz_mul_c)\n";
  fprintf fmt "       (castm (diff_r n m) (extend_tr x (snd d)))\n";
  fprintf fmt "       (castm (diff_l n m) (extend_tr y (fst d)))).\n";
  fprintf fmt "\n";

  fprintf fmt " Definition mul := Eval lazy beta delta [iter0] in \n";
  fprintf fmt "  (iter0 t_ \n";
  for i = 0 to size do
    fprintf fmt "    (fun x y => reduce_%i (w%i_mul_c x y)) \n" (i + 1) i;
    fprintf fmt "    (fun n x y => w%i_mul n y x)\n" i;
    fprintf fmt "    w%i_mul\n" i;
  done;
  fprintf fmt "    mulnm\n";
  fprintf fmt "    (fun _ => N0 w_0)\n";
  fprintf fmt "    (fun _ => N0 w_0)\n";
  fprintf fmt "  ).\n";
  fprintf fmt "\n";
  if gen_proof then
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

  fprintf fmt "  Lemma nmake_op_WW: forall ww ww1 n x y,\n";
  fprintf fmt "    znz_to_Z (nmake_op ww ww1 (S n)) (WW x y) =\n";
  fprintf fmt "    znz_to_Z (nmake_op ww ww1 n) x * base (znz_digits (nmake_op ww ww1 n)) +\n";
  fprintf fmt "    znz_to_Z (nmake_op ww ww1 n) y.\n";
  fprintf fmt "    auto.\n";
  fprintf fmt "  Qed.\n";
  fprintf fmt "\n";

  for i = 0 to size do
    fprintf fmt "  Lemma extend%in_spec: forall n x1,\n" i;
    fprintf fmt "  znz_to_Z (nmake_op _ w%i_op (S n)) (extend%i n x1) = \n" i i;
    fprintf fmt "  znz_to_Z w%i_op x1.\n" i;
    fprintf fmt "  Proof.\n";
    fprintf fmt "    intros n1 x2; rewrite nmake_gen.\n";
    fprintf fmt "    unfold extend%i.\n" i;
    fprintf fmt "    rewrite GenBase.spec_extend; auto.\n";
    if (i == 0) then 
      fprintf fmt "    intros l; simpl; unfold w_0; rewrite (spec_0 w0_spec); ring.\n";
    fprintf fmt "  Qed.\n";
    fprintf fmt "\n";

  done;

  fprintf fmt "  Lemma spec_muln:\n";
  fprintf fmt "    forall n (x: word _ (S n)) y,\n";
  fprintf fmt "     [%sn (S n) (znz_mul_c (make_op n) x y)] = [%sn n x] * [%sn n y].\n" c c c;
  fprintf fmt "  Proof.\n";
  fprintf fmt "    intros n x y; unfold to_Z.\n";
  fprintf fmt "    rewrite <- (spec_mul_c (wn_spec n)).\n";
  fprintf fmt "    rewrite make_op_S.\n";
  fprintf fmt "    case znz_mul_c; auto.\n";
  fprintf fmt "  Qed.\n";
  end;

  fprintf fmt "  Theorem spec_mul: forall x y, [mul x y] = [x] * [y].\n";
  if gen_proof then
  begin
  fprintf fmt "  Proof.\n";
  for i = 0 to size do
     fprintf fmt "    assert(F%i: \n" i;
     fprintf fmt "    forall n x y,\n";
     if i <> size then
       fprintf fmt "    Z_of_nat n <= %i -> "   (size - i);
     fprintf fmt "    [w%i_mul n x y] = eval%in (S n) x * [%s%i y]).\n" i i c i;
     if i == size then
       fprintf fmt "    intros n x y; unfold w%i_mul.\n" i
     else
       fprintf fmt "    intros n x y H; unfold w%i_mul.\n" i;
     if i == 0 then 
       fprintf fmt "    generalize (spec_w%i_mul_add_n1 (S n) x y w_0).\n" i
     else
       fprintf fmt "    generalize (spec_w%i_mul_add_n1 (S n) x y W0).\n" i;
     fprintf fmt "    case w%i_mul_add_n1; intros x1 y1.\n" i;
     fprintf fmt "    change (znz_to_Z (nmake_op _ w%i_op (S n)) x) with (eval%in (S n) x).\n" i i;
     fprintf fmt "    change (znz_to_Z w%i_op y) with ([%s%i y]).\n" i c i;
     if i == 0 then
       fprintf fmt "    unfold w_0; rewrite (spec_0 w0_spec); rewrite Zplus_0_r.\n"
     else
       fprintf fmt "    change (znz_to_Z w%i_op W0) with 0; rewrite Zplus_0_r.\n" i;
     fprintf fmt "    intros H1; rewrite <- H1; clear H1.\n";
     fprintf fmt "    generalize (spec_w%i_eq0 x1); case w%i_eq0; intros HH.\n" i i;
     fprintf fmt "    unfold to_Z in HH; rewrite HH.\n";
     if i == size then
       begin 
         fprintf fmt "    rewrite spec_eval%in; unfold eval%in, nmake_op%i; auto.\n" i i i;
         fprintf fmt "    rewrite spec_eval%in; unfold eval%in, nmake_op%i.\n" i i i
       end
     else
       begin
       fprintf fmt "    rewrite to_Z%i_spec; auto with zarith.\n" i;
       fprintf fmt "    rewrite to_Z%i_spec; try (rewrite inj_S; auto with zarith).\n" i
       end;
     fprintf fmt "    rewrite nmake_op_WW; rewrite extend%in_spec; auto.\n" i;
  done;
  fprintf fmt "    refine (spec_iter0 t_ (fun x y res => [res] = x * y)\n";
  for i = 0 to size do
    fprintf fmt "    (fun x y => reduce_%i (w%i_mul_c x y)) \n" (i + 1) i;
    fprintf fmt "    (fun n x y => w%i_mul n y x)\n" i;
    fprintf fmt "    w%i_mul _ _ _\n" i;
  done;
  fprintf fmt "    mulnm _\n";
  fprintf fmt "    (fun _ => N0 w_0) _\n";
  fprintf fmt "    (fun _ => N0 w_0) _\n";
  fprintf fmt "  ).\n";
  for i = 0 to size do
     fprintf fmt "    intros x y; rewrite spec_reduce_%i.\n" (i + 1);
     fprintf fmt "    unfold w%i_mul_c, to_Z.\n" i;
     fprintf fmt "    generalize (spec_mul_c w%i_spec x y).\n" i;
     fprintf fmt "    intros HH; rewrite <- HH; clear HH; auto.\n";
     if i == size then
       begin
         fprintf fmt "    intros n x y; rewrite F%i; auto with zarith.\n" i;
         fprintf fmt "    intros n x y; rewrite F%i; auto with zarith. \n" i;
       end
     else
       begin
         fprintf fmt "    intros n x y H; rewrite F%i; auto with zarith.\n" i;
         fprintf fmt "    intros n x y H; rewrite F%i; auto with zarith. \n" i;
       end;
  done;
  fprintf fmt "    intros n m x y; unfold mulnm.\n";
  fprintf fmt "    rewrite spec_reduce_n.\n";
  fprintf fmt "    rewrite <- (spec_cast_l n m x).\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y).\n";
  fprintf fmt "    rewrite spec_muln; rewrite spec_cast_l; rewrite spec_cast_r; auto.\n";
  fprintf fmt "    intros x; unfold to_Z, w_0; rewrite (spec_0 w0_spec); ring.\n";
  fprintf fmt "    intros x; unfold to_Z, w_0; rewrite (spec_0 w0_spec); ring.\n";
  fprintf fmt "  Qed.\n";
  end
  else
  fprintf fmt "  Admitted.\n";  
  fprintf fmt "\n";

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Square                            *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";
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

  fprintf fmt " Theorem spec_square: forall x, [square x] = [x] * [x].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt "  intros x; case x; unfold square; clear x.\n";
  fprintf fmt "  intros x; rewrite spec_reduce_1; unfold to_Z.\n";
  fprintf fmt "   exact (spec_square_c w%i_spec x).\n" 0;
  for i = 1 to size do
    fprintf fmt "  intros x; unfold to_Z.\n";
    fprintf fmt "    exact (spec_square_c w%i_spec x).\n" i;
  done;
  fprintf fmt "  intros n x; unfold to_Z.\n";
  fprintf fmt "    rewrite make_op_S.\n";
  fprintf fmt "    exact (spec_square_c (wn_spec n) x).\n";
  fprintf fmt "Qed.\n";
  end
  else
  fprintf fmt "Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Power                             *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";
  fprintf fmt " Fixpoint power_pos (x:%s) (p:positive) {struct p} : %s :=\n"
    t t;
  fprintf fmt "  match p with\n";
  fprintf fmt "  | xH => x\n";
  fprintf fmt "  | xO p => square (power_pos x p)\n";
  fprintf fmt "  | xI p => mul (square (power_pos x p)) x\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_power_pos: forall x n, [power_pos x n] = [x] ^ Zpos n.\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x n; generalize x; elim n; clear n x; simpl power_pos.\n";
  fprintf fmt " intros; rewrite spec_mul; rewrite spec_square; rewrite H.\n";
  fprintf fmt " rewrite Zpos_xI; rewrite Zpower_exp; auto with zarith.\n";
  fprintf fmt " rewrite (Zmult_comm 2); rewrite ZPowerAux.Zpower_mult; auto with zarith.\n";
  fprintf fmt " rewrite ZAux.Zpower_2; rewrite ZAux.Zpower_exp_1; auto.\n";
  fprintf fmt " intros; rewrite spec_square; rewrite H.\n";
  fprintf fmt " rewrite Zpos_xO; auto with zarith.\n";
  fprintf fmt " rewrite (Zmult_comm 2); rewrite ZPowerAux.Zpower_mult; auto with zarith.\n";
  fprintf fmt " rewrite ZAux.Zpower_2; auto.\n";
  fprintf fmt " intros; rewrite ZAux.Zpower_exp_1; auto.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end
  else
  fprintf fmt " Admitted.\n";  
  fprintf fmt "\n";

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Square root                       *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

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



  fprintf fmt " Theorem spec_sqrt: forall x, [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; unfold sqrt; case x; clear x.\n";
  for i = 0 to size do
    fprintf fmt " intros x; rewrite spec_reduce_%i; exact (spec_sqrt w%i_spec x).\n" i i;
  done;
  fprintf fmt " intros n x; rewrite spec_reduce_n; exact (spec_sqrt (wn_spec n) x).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt "Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Division                          *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

    
  (* Division *)
  for i = 0 to size do
    fprintf fmt " Definition w%i_div_gt := w%i_op.(znz_div_gt).\n" i i
  done;
  fprintf fmt "\n";
  
  if gen_proof then
  begin
  fprintf fmt " Let spec_divn1 ww (ww_op: znz_op ww) (ww_spec: znz_spec ww_op) := \n";
  fprintf fmt "   (spec_gen_divn1 \n";
  fprintf fmt "    ww_op.(znz_zdigits) ww_op.(znz_0)\n";
  fprintf fmt "    ww_op.(znz_WW) ww_op.(znz_head0)\n";
  fprintf fmt "    ww_op.(znz_add_mul_div) ww_op.(znz_div21)\n";
  fprintf fmt "    ww_op.(znz_compare) ww_op.(znz_sub) (znz_to_Z ww_op)\n";
  fprintf fmt "    (spec_to_Z ww_spec) \n";
  fprintf fmt "    (spec_zdigits ww_spec)\n";
  fprintf fmt "   (spec_0 ww_spec) (spec_WW ww_spec) (spec_head0 ww_spec)\n";
  fprintf fmt "   (spec_add_mul_div ww_spec) (spec_div21 ww_spec) \n";
  fprintf fmt "    (ZnZ.spec_compare ww_spec) (ZnZ.spec_sub ww_spec)).\n";
  fprintf fmt "  \n";
  end;

  for i = 0 to size do
    fprintf fmt " Definition w%i_divn1 n x y :=\n"  i;
    fprintf fmt "  let (u, v) :=\n";
    fprintf fmt "  gen_divn1 w%i_op.(znz_zdigits) w%i_op.(znz_0)\n" i i;
    fprintf fmt "    w%i_op.(znz_WW) w%i_op.(znz_head0)\n" i i;
    fprintf fmt "    w%i_op.(znz_add_mul_div) w%i_op.(znz_div21)\n" i i;
    fprintf fmt "    w%i_op.(znz_compare) w%i_op.(znz_sub) (S n) x y in\n" i i;
    if i == size then
      fprintf fmt "   (%sn _ u, %s%i v).\n" c c i
    else
      fprintf fmt "   (to_Z%i _ u, %s%i v).\n" i c i;
  done;
  fprintf fmt "\n";


  if gen_proof then
  begin
  for i = 0 to size do
    fprintf fmt " Lemma spec_get_end%i: forall n x y,\n" i;
    fprintf fmt "    eval%in n x  <= [%s%i y] -> \n" i c i;
    fprintf fmt "     [%s%i (GenBase.get_low %s n x)] = eval%in n x.\n" c i (pz i) i;
    fprintf fmt " Proof.\n";
    fprintf fmt " intros n x y H.\n";
    fprintf fmt " rewrite spec_gen_eval%in; unfold to_Z.\n" i;
    fprintf fmt " apply GenBase.spec_get_low.\n";
    fprintf fmt " exact (spec_0 w%i_spec).\n" i;
    fprintf fmt " exact (spec_to_Z w%i_spec).\n" i;
    fprintf fmt " apply Zle_lt_trans with [%s%i y]; auto.\n" c i;
    fprintf fmt "   rewrite <- spec_gen_eval%in; auto.\n" i;
    fprintf fmt " unfold to_Z; case (spec_to_Z w%i_spec y); auto.\n" i;
    fprintf fmt " Qed.\n";
    fprintf fmt "\n";
  done ;
  end;

  for i = 0 to size do
    fprintf fmt " Let div_gt%i x y := let (u,v) := (w%i_div_gt x y) in (reduce_%i u, reduce_%i v).\n" i i i i;
  done;
  fprintf fmt "\n";


  fprintf fmt " Let div_gtnm n m wx wy :=\n";
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "    let (q, r):= op.(znz_div_gt)\n";
  fprintf fmt "         (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "         (castm (diff_l n m) (extend_tr wy (fst d))) in\n";
  fprintf fmt "    (reduce_n mn q, reduce_n mn r).\n";
  fprintf fmt "\n";

  fprintf fmt " Definition div_gt := Eval lazy beta delta [iter] in\n";
  fprintf fmt "   (iter _ \n";
  for i = 0 to size do 
    fprintf fmt "      div_gt%i\n" i;
    fprintf fmt "      (fun n x y => div_gt%i x (GenBase.get_low %s (S n) y))\n" i (pz i);
    fprintf fmt "      w%i_divn1\n" i;
  done;
  fprintf fmt "      div_gtnm).\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_div_gt: forall x y,\n";
  fprintf fmt "       [x] > [y] -> 0 < [y] ->\n";
  fprintf fmt "      let (q,r) := div_gt x y in\n";
  fprintf fmt "      [q] = [x] / [y] /\\ [r] = [x] mod [y].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (FO:\n";
  fprintf fmt "   forall x y, [x] > [y] -> 0 < [y] ->\n";
  fprintf fmt "      let (q,r) := div_gt x y in\n";
  fprintf fmt "      [x] = [q] * [y] + [r] /\\ 0 <= [r] < [y]).\n";
  fprintf fmt "  refine (spec_iter (t_*t_) (fun x y res => x > y -> 0 < y ->\n";  fprintf fmt "      let (q,r) := res in\n";
  fprintf fmt "      x = [q] * y + [r] /\\ 0 <= [r] < y)\n";
  for i = 0 to size do 
    fprintf fmt "      div_gt%i\n" i;
    fprintf fmt "      (fun n x y => div_gt%i x (GenBase.get_low %s (S n) y))\n" i (pz i);
    fprintf fmt "      w%i_divn1 _ _ _\n" i;
  done;
  fprintf fmt "      div_gtnm _).\n";
  for i = 0 to size do
    fprintf fmt "  intros x y H1 H2; unfold div_gt%i, w%i_div_gt.\n" i i;
    fprintf fmt "    generalize (spec_div_gt w%i_spec x y H1 H2); case znz_div_gt.\n" i;
    fprintf fmt "    intros xx yy; repeat rewrite spec_reduce_%i; auto.\n" i;
    if i == size then
      fprintf fmt "  intros n x y H2 H3; unfold div_gt%i, w%i_div_gt.\n" i i
    else
      fprintf fmt "  intros n x y H1 H2 H3; unfold div_gt%i, w%i_div_gt.\n" i i;
    fprintf fmt "    generalize (spec_div_gt w%i_spec x \n" i;
    fprintf fmt "                (GenBase.get_low %s (S n) y)).\n" (pz i);
    fprintf fmt "    ";
    for j = 0 to i do
      fprintf fmt "unfold w%i;" (i-j); 
    done;
    fprintf fmt "case znz_div_gt.\n";
    fprintf fmt "    intros xx yy H4; repeat rewrite spec_reduce_%i.\n" i;
    fprintf fmt "    generalize (spec_get_end%i (S n) y x); unfold to_Z; intros H5.\n" i;
    fprintf fmt "    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.\n";
    if i == size then
      fprintf fmt "  intros n x y H2 H3.\n"
    else
      fprintf fmt "  intros n x y H1 H2 H3.\n";
    fprintf fmt "    generalize\n";
    fprintf fmt "     (spec_divn1 w%i w%i_op w%i_spec (S n) x y H3).\n" i i i;
    fprintf fmt "    unfold w%i_divn1;" i;
    for j = 0 to i do
      fprintf fmt "unfold w%i;" (i-j); 
    done;
    fprintf fmt " case gen_divn1.\n";
    fprintf fmt "    intros xx yy H4.\n";
    if i == size then
      begin
        fprintf fmt "    repeat rewrite <- spec_gen_eval%in in H4; auto.\n" i;
        fprintf fmt "    rewrite spec_eval%in; auto.\n" i;
      end
    else
      begin
       fprintf fmt "    rewrite to_Z%i_spec; auto with zarith.\n" i;
       fprintf fmt "    repeat rewrite <- spec_gen_eval%in in H4; auto.\n" i;
      end;
  done;
  fprintf fmt "  intros n m x y H1 H2; unfold div_gtnm.\n";
  fprintf fmt "    generalize (spec_div_gt (wn_spec (Max.max n m))\n";
  fprintf fmt "                   (castm (diff_r n m)\n";
  fprintf fmt "                     (extend_tr x (snd (diff n m))))\n";
  fprintf fmt "                   (castm (diff_l n m)\n";
  fprintf fmt "                     (extend_tr y (fst (diff n m))))).\n";
  fprintf fmt "    case znz_div_gt.\n";
  fprintf fmt "    intros xx yy HH.\n";
  fprintf fmt "    repeat rewrite spec_reduce_n.\n";
  fprintf fmt "    rewrite <- (spec_cast_l n m x).\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y).\n";
  fprintf fmt "    unfold to_Z; apply HH.\n";
  fprintf fmt "    rewrite <- (spec_cast_l n m x) in H1; auto.\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y) in H1; auto.\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y) in H2; auto.\n";
  fprintf fmt "  intros x y H1 H2; generalize (FO x y H1 H2); case div_gt.\n";
  fprintf fmt "  intros q r (H3, H4); split.\n";
  fprintf fmt "  apply (ZDivModAux.Zdiv_unique [x] [y] [q] [r]); auto.\n";
  fprintf fmt "  rewrite Zmult_comm; auto.\n";
  fprintf fmt "  apply (ZDivModAux.Zmod_unique [x] [y] [q] [r]); auto.\n";
  fprintf fmt "  rewrite Zmult_comm; auto.\n";
  fprintf fmt "  Qed.\n";
  end
  else
  fprintf fmt "  Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition div_eucl x y :=\n";
  fprintf fmt "  match compare x y with\n";
  fprintf fmt "  | Eq => (one, zero)\n";
  fprintf fmt "  | Lt => (zero, x)\n";
  fprintf fmt "  | Gt => div_gt x y\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_div_eucl: forall x y,\n";
  fprintf fmt "      0 < [y] ->\n";
  fprintf fmt "      let (q,r) := div_eucl x y in\n";
  fprintf fmt "      [q] = [x] / [y] /\\ [r] = [x] mod [y].\n";
  if gen_proof then 
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F0: [zero] = 0).\n";
  fprintf fmt "   exact (spec_0 w0_spec).\n";
  fprintf fmt " assert (F1: [one] = 1).\n";
  fprintf fmt "   exact (spec_1 w0_spec).\n";
  fprintf fmt " intros x y H; generalize (spec_compare x y);\n";
  fprintf fmt "   unfold div_eucl; case compare; try rewrite F0;\n";
  fprintf fmt "   try rewrite F1; intros; try split; auto with zarith.\n";
  fprintf fmt " rewrite H0; apply sym_equal; apply Z_div_same; auto with zarith.\n";
  fprintf fmt " rewrite H0; apply sym_equal; apply Z_mod_same; auto with zarith.\n";
  fprintf fmt " apply sym_equal; apply ZDivModAux.Zdiv_lt_0.\n";
  fprintf fmt " generalize (to_Z_pos x); auto with zarith.\n";
  fprintf fmt " apply sym_equal; apply ZAux.Zmod_def_small; auto with zarith.\n";
  fprintf fmt " generalize (to_Z_pos x); auto with zarith.\n";
  fprintf fmt " apply (spec_div_gt x y); auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition div x y := fst (div_eucl x y).\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_div:\n";
  fprintf fmt "   forall x y, 0 < [y] -> [div x y] = [x] / [y].\n";
  if gen_proof then 
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x y H1; unfold div; generalize (spec_div_eucl x y H1);\n";
  fprintf fmt "   case div_eucl; simpl fst.\n";
  fprintf fmt " intros xx yy (H2, H3); auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Modulo                            *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

  for i = 0 to size do
    fprintf fmt " Definition w%i_mod_gt := w%i_op.(znz_mod_gt).\n" i i
  done;
  fprintf fmt "\n";

  for i = 0 to size do
    fprintf fmt " Definition w%i_modn1 :=\n" i;
    fprintf fmt "  gen_modn1 w%i_op.(znz_zdigits) w%i_op.(znz_0)\n" i i;
    fprintf fmt "    w%i_op.(znz_head0) w%i_op.(znz_add_mul_div) w%i_op.(znz_div21)\n" i i i;
    fprintf fmt "    w%i_op.(znz_compare) w%i_op.(znz_sub).\n" i i;
  done;
  fprintf fmt "\n";

  fprintf fmt " Let mod_gtnm n m wx wy :=\n";
  fprintf fmt "    let mn := Max.max n m in\n";
  fprintf fmt "    let d := diff n m in\n";
  fprintf fmt "    let op := make_op mn in\n";
  fprintf fmt "    reduce_n mn (op.(znz_mod_gt)\n";
  fprintf fmt "         (castm (diff_r n m) (extend_tr wx (snd d)))\n";
  fprintf fmt "         (castm (diff_l n m) (extend_tr wy (fst d)))).\n";
  fprintf fmt "\n";

  fprintf fmt " Definition mod_gt := Eval lazy beta delta[iter] in\n";
  fprintf fmt "   (iter _ \n";
  for i = 0 to size do
    fprintf fmt "      (fun x y => reduce_%i (w%i_mod_gt x y))\n" i i;
    fprintf fmt "      (fun n x y => reduce_%i (w%i_mod_gt x (GenBase.get_low %s (S n) y)))\n" i i (pz i);
    fprintf fmt "      (fun n x y => reduce_%i (w%i_modn1 (S n) x y))\n" i i;
  done;
  fprintf fmt "      mod_gtnm).\n";
  fprintf fmt "\n";

  if gen_proof then
  begin
  fprintf fmt " Let spec_modn1 ww (ww_op: znz_op ww) (ww_spec: znz_spec ww_op) := \n";
  fprintf fmt "   (spec_gen_modn1 \n";
  fprintf fmt "    ww_op.(znz_zdigits) ww_op.(znz_0)\n";
  fprintf fmt "    ww_op.(znz_WW) ww_op.(znz_head0)\n";
  fprintf fmt "    ww_op.(znz_add_mul_div) ww_op.(znz_div21)\n";
  fprintf fmt "    ww_op.(znz_compare) ww_op.(znz_sub) (znz_to_Z ww_op)\n";
  fprintf fmt "    (spec_to_Z ww_spec) \n";
  fprintf fmt "    (spec_zdigits ww_spec)\n";
  fprintf fmt "   (spec_0 ww_spec) (spec_WW ww_spec) (spec_head0 ww_spec)\n";
  fprintf fmt "   (spec_add_mul_div ww_spec) (spec_div21 ww_spec) \n";
  fprintf fmt "    (ZnZ.spec_compare ww_spec) (ZnZ.spec_sub ww_spec)).\n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Theorem spec_mod_gt:\n";
  fprintf fmt "   forall x y, [x] > [y] -> 0 < [y] -> [mod_gt x y] = [x] mod [y].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " refine (spec_iter _ (fun x y res => x > y -> 0 < y ->\n";
  fprintf fmt "      [res] = x mod y)\n";
  for i = 0 to size do
    fprintf fmt "      (fun x y => reduce_%i (w%i_mod_gt x y))\n" i i;
    fprintf fmt "      (fun n x y => reduce_%i (w%i_mod_gt x (GenBase.get_low %s (S n) y)))\n" i i (pz i);
    fprintf fmt "      (fun n x y => reduce_%i (w%i_modn1 (S n) x y)) _ _ _\n" i i;
  done;
  fprintf fmt "      mod_gtnm _).\n";
  for i = 0 to size do
    fprintf fmt " intros x y H1 H2; rewrite spec_reduce_%i.\n" i;
    fprintf fmt "   exact (spec_mod_gt w%i_spec x y H1 H2).\n" i;
    if i == size then
      fprintf fmt " intros n x y H2 H3; rewrite spec_reduce_%i.\n" i
    else
      fprintf fmt " intros n x y H1 H2 H3; rewrite spec_reduce_%i.\n" i;
    fprintf fmt " unfold w%i_mod_gt.\n" i;
    fprintf fmt " rewrite <- (spec_get_end%i (S n) y x); auto with zarith.\n" i;
    fprintf fmt " unfold to_Z; apply (spec_mod_gt w%i_spec); auto.\n" i;
    fprintf fmt " rewrite <- (spec_get_end%i (S n) y x) in H2; auto with zarith.\n" i;
    fprintf fmt " rewrite <- (spec_get_end%i (S n) y x) in H3; auto with zarith.\n" i;
    if i == size then
      fprintf fmt " intros n x y H2 H3; rewrite spec_reduce_%i.\n" i
    else 
      fprintf fmt " intros n x y H1 H2 H3; rewrite spec_reduce_%i.\n" i;
    fprintf fmt " unfold w%i_modn1, to_Z; rewrite spec_gen_eval%in.\n" i i;
    fprintf fmt " apply (spec_modn1 _ _ w%i_spec); auto.\n" i;
  done;
  fprintf fmt " intros n m x y H1 H2; unfold mod_gtnm.\n";
  fprintf fmt "    repeat rewrite spec_reduce_n.\n";
  fprintf fmt "    rewrite <- (spec_cast_l n m x).\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y).\n";
  fprintf fmt "    unfold to_Z; apply (spec_mod_gt (wn_spec (Max.max n m))).\n";
  fprintf fmt "    rewrite <- (spec_cast_l n m x) in H1; auto.\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y) in H1; auto.\n";
  fprintf fmt "    rewrite <- (spec_cast_r n m y) in H2; auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition modulo x y := \n";
  fprintf fmt "  match compare x y with\n";
  fprintf fmt "  | Eq => zero\n";
  fprintf fmt "  | Lt => x\n";
  fprintf fmt "  | Gt => mod_gt x y\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_modulo:\n";
  fprintf fmt "   forall x y, 0 < [y] -> [modulo x y] = [x] mod [y].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F0: [zero] = 0).\n";
  fprintf fmt "   exact (spec_0 w0_spec).\n";
  fprintf fmt " assert (F1: [one] = 1).\n";
  fprintf fmt "   exact (spec_1 w0_spec).\n";
  fprintf fmt " intros x y H; generalize (spec_compare x y);\n";
  fprintf fmt "   unfold modulo; case compare; try rewrite F0;\n";
  fprintf fmt "   try rewrite F1; intros; try split; auto with zarith.\n";
  fprintf fmt " rewrite H0; apply sym_equal; apply Z_mod_same; auto with zarith.\n";
  fprintf fmt " apply sym_equal; apply ZAux.Zmod_def_small; auto with zarith.\n";
  fprintf fmt " generalize (to_Z_pos x); auto with zarith.\n";
  fprintf fmt " apply spec_mod_gt; auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                           Gcd                               *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

  fprintf fmt " Definition digits x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i _ => w%i_op.(znz_digits)\n" c i i;
  done;
  fprintf fmt "  | %sn n _ => (make_op n).(znz_digits)\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_digits: forall x, 0 <= [x] < 2 ^  Zpos (digits x).\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; clear x.\n";
  for i = 0 to size do
    fprintf fmt "  intros x; unfold to_Z, digits;\n";
    fprintf fmt "   generalize (spec_to_Z w%i_spec x); unfold base; intros H; exact H.\n" i;
  done;
  fprintf fmt "  intros n x; unfold to_Z, digits;\n";
  fprintf fmt "   generalize (spec_to_Z (wn_spec n) x); unfold base; intros H; exact H.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
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

  if gen_proof then
  begin
  fprintf fmt " Theorem Zspec_gcd_gt_body: forall a b cont p,\n";
  fprintf fmt "    [a] > [b] -> [a] < 2 ^ p ->\n";
  fprintf fmt "      (forall a1 b1, [a1] < 2 ^ (p - 1) -> [a1] > [b1] ->\n";
  fprintf fmt "         Zis_gcd  [a1] [b1] [cont a1 b1]) ->                   \n";
  fprintf fmt "      Zis_gcd [a] [b] [gcd_gt_body a b cont].\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F1: [zero] = 0).\n";
  fprintf fmt "   unfold zero, w_0, to_Z; rewrite (spec_0 w0_spec); auto.\n";
  fprintf fmt " intros a b cont p H2 H3 H4; unfold gcd_gt_body.\n";
  fprintf fmt " generalize (spec_compare b zero); case compare; try rewrite F1.\n";
  fprintf fmt "   intros HH; rewrite HH; apply Zis_gcd_0.\n";
  fprintf fmt " intros HH; absurd (0 <= [b]); auto with zarith.\n";
  fprintf fmt " case (spec_digits b); auto with zarith.\n";
  fprintf fmt " intros H5; generalize (spec_compare (mod_gt a b) zero); \n";
  fprintf fmt "   case compare; try rewrite F1.\n";
  fprintf fmt " intros H6; rewrite <- (Zmult_1_r [b]).\n";
  fprintf fmt " rewrite (Z_div_mod_eq [a] [b]); auto with zarith.\n";
  fprintf fmt " rewrite <- spec_mod_gt; auto with zarith.\n";
  fprintf fmt " rewrite H6; rewrite Zplus_0_r.\n";
  fprintf fmt " apply Zis_gcd_mult; apply Zis_gcd_1.\n";
  fprintf fmt " intros; apply False_ind.\n";
  fprintf fmt " case (spec_digits (mod_gt a b)); auto with zarith.\n";
  fprintf fmt " intros H6; apply GenDiv.Zis_gcd_mod; auto with zarith.\n";
  fprintf fmt " apply GenDiv.Zis_gcd_mod; auto with zarith.\n";
  fprintf fmt " rewrite <- spec_mod_gt; auto with zarith.\n";
  fprintf fmt " assert (F2: [b] > [mod_gt a b]).\n";
  fprintf fmt "   case (Z_mod_lt [a] [b]); auto with zarith.\n";
  fprintf fmt "   repeat rewrite <- spec_mod_gt; auto with zarith.\n";
  fprintf fmt " assert (F3: [mod_gt a b] > [mod_gt b  (mod_gt a b)]).\n";
  fprintf fmt "   case (Z_mod_lt [b] [mod_gt a b]); auto with zarith.\n";
  fprintf fmt "   rewrite <- spec_mod_gt; auto with zarith.\n";
  fprintf fmt " repeat rewrite <- spec_mod_gt; auto with zarith.\n";
  fprintf fmt " apply H4; auto with zarith.\n";
  fprintf fmt " apply Zmult_lt_reg_r with 2; auto with zarith.\n";
  fprintf fmt " apply Zle_lt_trans with ([b] + [mod_gt a b]); auto with zarith.\n";
  fprintf fmt " apply Zle_lt_trans with (([a]/[b]) * [b] + [mod_gt a b]); auto with zarith.\n";
  fprintf fmt "   apply Zplus_le_compat_r.\n";
  fprintf fmt " pattern [b] at 1; rewrite <- (Zmult_1_l [b]).\n";
  fprintf fmt " apply Zmult_le_compat_r; auto with zarith.\n";
  fprintf fmt " case (Zle_lt_or_eq 0 ([a]/[b])); auto with zarith.\n";
  fprintf fmt " intros HH; rewrite (Z_div_mod_eq [a] [b]) in H2;\n";
  fprintf fmt "   try rewrite <- HH in H2; auto with zarith.\n";
  fprintf fmt " case (Z_mod_lt [a] [b]); auto with zarith.\n";
  fprintf fmt " rewrite Zmult_comm; rewrite spec_mod_gt; auto with zarith.\n";
  fprintf fmt " rewrite <- Z_div_mod_eq; auto with zarith.\n";
  fprintf fmt " pattern 2 at 2; rewrite <- (Zpower_exp_1 2).\n";
  fprintf fmt " rewrite <- Zpower_exp; auto with zarith.\n";
  fprintf fmt " ring_simplify (p - 1 + 1); auto.\n";
  fprintf fmt " case (Zle_lt_or_eq 0 p); auto with zarith.\n";
  fprintf fmt " generalize H3; case p; simpl Zpower; auto with zarith.\n";
  fprintf fmt " intros HH; generalize H3; rewrite <- HH; simpl Zpower; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Fixpoint gcd_gt_aux (p:positive) (cont:t->t->t) (a b:t) {struct p} : t :=\n";
  fprintf fmt "  gcd_gt_body a b\n";
  fprintf fmt "    (fun a b =>\n";
  fprintf fmt "       match p with\n";
  fprintf fmt "       | xH => cont a b\n";
  fprintf fmt "       | xO p => gcd_gt_aux p (gcd_gt_aux p cont) a b\n";
  fprintf fmt "       | xI p => gcd_gt_aux p (gcd_gt_aux p cont) a b\n";
  fprintf fmt "       end).\n";
  fprintf fmt "\n";
  
  if gen_proof then
  begin
  fprintf fmt " Theorem Zspec_gcd_gt_aux: forall p n a b cont,\n";
  fprintf fmt "    [a] > [b] -> [a] < 2 ^ (Zpos p + n) ->\n";
  fprintf fmt "      (forall a1 b1, [a1] < 2 ^ n -> [a1] > [b1] ->\n";
  fprintf fmt "            Zis_gcd [a1] [b1] [cont a1 b1]) ->\n";
  fprintf fmt "          Zis_gcd [a] [b] [gcd_gt_aux p cont a b].\n";
  fprintf fmt " intros p; elim p; clear p.\n";
  fprintf fmt " intros p Hrec n a b cont H2 H3 H4.\n";
  fprintf fmt "   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xI p) + n); auto.\n";
  fprintf fmt "   intros a1 b1 H6 H7.\n";
  fprintf fmt "     apply Hrec with (Zpos p + n); auto.\n";
  fprintf fmt "       replace (Zpos p + (Zpos p + n)) with\n";
  fprintf fmt "         (Zpos (xI p) + n  - 1); auto.\n";
  fprintf fmt "       rewrite Zpos_xI; ring.\n";
  fprintf fmt "   intros a2 b2 H9 H10.\n";
  fprintf fmt "     apply Hrec with n; auto.\n";
  fprintf fmt " intros p Hrec n a b cont H2 H3 H4.\n";
  fprintf fmt "   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xO p) + n); auto.\n";
  fprintf fmt "   intros a1 b1 H6 H7.\n";
  fprintf fmt "     apply Hrec with (Zpos p + n - 1); auto.\n";
  fprintf fmt "       replace (Zpos p + (Zpos p + n - 1)) with\n";
  fprintf fmt "         (Zpos (xO p) + n  - 1); auto.\n";
  fprintf fmt "       rewrite Zpos_xO; ring.\n";
  fprintf fmt "   intros a2 b2 H9 H10.\n";
  fprintf fmt "     apply Hrec with (n - 1); auto.\n";
  fprintf fmt "       replace (Zpos p + (n - 1)) with\n";
  fprintf fmt "         (Zpos p + n  - 1); auto with zarith.\n";
  fprintf fmt "   intros a3 b3 H12 H13; apply H4; auto with zarith.\n";
  fprintf fmt "    apply Zlt_le_trans with (1 := H12).\n";
  fprintf fmt "    case (Zle_or_lt 1 n); intros HH.\n";
  fprintf fmt "    apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "    apply Zle_trans with 0; auto with zarith.\n";
  fprintf fmt "    assert (HH1: n - 1 < 0); auto with zarith.\n";
  fprintf fmt "    generalize HH1; case (n - 1); auto with zarith.\n";
  fprintf fmt "    intros p1 HH2; discriminate.\n";
  fprintf fmt " intros n a b cont H H2 H3.\n";
  fprintf fmt "  simpl gcd_gt_aux.\n";
  fprintf fmt "  apply Zspec_gcd_gt_body with (n + 1); auto with zarith.\n";
  fprintf fmt "  rewrite Zplus_comm; auto.\n";
  fprintf fmt "  intros a1 b1 H5 H6; apply H3; auto.\n";
  fprintf fmt "  replace n with (n + 1 - 1); auto; try ring.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";
  end;

  fprintf fmt " Definition gcd_cont a b :=\n";
  fprintf fmt "  match compare one b with\n";
  fprintf fmt "  | Eq => one\n";
  fprintf fmt "  | _ => a\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition gcd_gt a b := gcd_gt_aux (digits a) gcd_cont a b.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_gcd_gt: forall a b,\n";
  fprintf fmt "   [a] > [b] -> [gcd_gt a b] = Zgcd [a] [b].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros a b H2.\n";
  fprintf fmt " case (spec_digits (gcd_gt a b)); intros H3 H4.\n";
  fprintf fmt " case (spec_digits a); intros H5 H6.\n";
  fprintf fmt " apply sym_equal; apply Zis_gcd_gcd; auto with zarith.\n";
  fprintf fmt " unfold gcd_gt; apply Zspec_gcd_gt_aux with 0; auto with zarith.\n";
  fprintf fmt " intros a1 a2; rewrite Zpower_exp_0.\n";
  fprintf fmt " case (spec_digits a2); intros H7 H8;\n";
  fprintf fmt "   intros; apply False_ind; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition gcd a b :=\n";
  fprintf fmt "  match compare a b with\n";
  fprintf fmt "  | Eq => a\n";
  fprintf fmt "  | Lt => gcd_gt b a\n";
  fprintf fmt "  | Gt => gcd_gt a b\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_gcd: forall a b, [gcd a b] = Zgcd [a] [b].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros a b.\n";
  fprintf fmt " case (spec_digits a); intros H1 H2.\n";
  fprintf fmt " case (spec_digits b); intros H3 H4.\n";
  fprintf fmt " unfold gcd; generalize (spec_compare a b); case compare.\n";
  fprintf fmt " intros HH; rewrite HH; apply sym_equal; apply Zis_gcd_gcd; auto.\n";
  fprintf fmt "   apply Zis_gcd_refl.\n";
  fprintf fmt " intros; apply trans_equal with (Zgcd [b] [a]).\n";
  fprintf fmt "   apply spec_gcd_gt; auto with zarith.\n";
  fprintf fmt " apply Zis_gcd_gcd; auto with zarith.\n";
  fprintf fmt " apply Zgcd_is_pos.\n";
  fprintf fmt " apply Zis_gcd_sym; apply Zgcd_is_gcd.\n";
  fprintf fmt " intros; apply spec_gcd_gt; auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                          Conversion                         *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";

  fprintf fmt " Definition pheight p := \n";
  fprintf fmt "   Peano.pred (nat_of_P (get_height w0_op.(znz_digits) (plength p))).\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem pheight_correct: forall p, \n";
  fprintf fmt "    Zpos p < 2 ^ (Zpos (znz_digits w0_op) * 2 ^ (Z_of_nat (pheight p))).\n";
  fprintf fmt " Proof.\n";
  fprintf fmt " intros p; unfold pheight.\n";
  fprintf fmt " assert (F1: forall x, Z_of_nat (Peano.pred (nat_of_P x)) = Zpos x - 1).\n";
  fprintf fmt "  intros x.\n";
  fprintf fmt "  assert (Zsucc (Z_of_nat (Peano.pred (nat_of_P x))) = Zpos x); auto with zarith.\n";
  fprintf fmt "    rewrite <- inj_S.\n";
  fprintf fmt "    rewrite <- (fun x => S_pred x 0); auto with zarith.\n";
  fprintf fmt "    rewrite Zpos_eq_Z_of_nat_o_nat_of_P; auto.\n";
  fprintf fmt "    apply lt_le_trans with 1%snat; auto with zarith.\n" "%";
  fprintf fmt "    exact (le_Pmult_nat x 1).\n";
  fprintf fmt "  rewrite F1; clear F1.\n";
  fprintf fmt " assert (F2:= (get_height_correct (znz_digits w0_op) (plength p))).\n";
  fprintf fmt " apply Zlt_le_trans with (Zpos (Psucc p)).\n";
  fprintf fmt "   rewrite Zpos_succ_morphism; auto with zarith.\n";
  fprintf fmt "  apply Zle_trans with (1 := plength_pred_correct (Psucc p)).\n";
  fprintf fmt " rewrite Ppred_succ.\n";
  fprintf fmt " apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition of_pos x :=\n";
  fprintf fmt "  let h := pheight x in\n";
  fprintf fmt "  match h with\n";
  for i = 0 to size do
    fprintf fmt "  | %i%snat => reduce_%i (snd (w%i_op.(znz_of_pos) x))\n" i "%" i i;
  done;
  fprintf fmt "  | _ =>\n";
  fprintf fmt "    let n := minus h %i in\n" (size + 1);
  fprintf fmt "    reduce_n n (snd ((make_op n).(znz_of_pos) x))\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";
 
  fprintf fmt " Theorem spec_of_pos: forall x,\n";
  fprintf fmt "   [of_pos x] = Zpos x.\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F := spec_more_than_1_digit w0_spec).\n";
  fprintf fmt " intros x; unfold of_pos; case_eq (pheight x).\n";
  for i = 0 to size do
    if i <> 0 then
      fprintf fmt " intros n; case n; clear n.\n";
    fprintf fmt " intros H1; rewrite spec_reduce_%i; unfold to_Z.\n" i;
    fprintf fmt " apply (znz_of_pos_correct w%i_spec).\n" i;
    fprintf fmt " apply Zlt_le_trans with (1 := pheight_correct x).\n";
    fprintf fmt "   rewrite H1; simpl Z_of_nat; change (2^%i) with (%s).\n" i (gen2 i);
    fprintf fmt "   unfold base.\n";
    fprintf fmt "   apply Zpower_le_monotone; split; auto with zarith.\n";
    if i <> 0 then
      begin
      fprintf fmt "   rewrite Zmult_comm; repeat rewrite <- Zmult_assoc.\n";
      fprintf fmt "     repeat rewrite <- Zpos_xO.\n";
      fprintf fmt "   refine (Zle_refl _).\n";
      end;
  done;
  fprintf fmt " intros n.\n";
  fprintf fmt " intros H1; rewrite spec_reduce_n; unfold to_Z.\n";
  fprintf fmt " simpl minus; rewrite <- minus_n_O.\n";
  fprintf fmt " apply (znz_of_pos_correct (wn_spec n)).\n";
  fprintf fmt " apply Zlt_le_trans with (1 := pheight_correct x).\n";
  fprintf fmt "   unfold base.\n";
  fprintf fmt "   apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "   split; auto with zarith.\n";
  fprintf fmt "   rewrite H1.\n";
  fprintf fmt "  elim n; clear n H1.\n";
  fprintf fmt "   simpl Z_of_nat; change (2^%i) with (%s).\n" (size + 1) (gen2 (size + 1));
  fprintf fmt "   rewrite Zmult_comm; repeat rewrite <- Zmult_assoc.\n";
  fprintf fmt "     repeat rewrite <- Zpos_xO.\n";
  fprintf fmt "   refine (Zle_refl _).\n";
  fprintf fmt "  intros n Hrec.\n";
  fprintf fmt "  rewrite make_op_S.\n";
  fprintf fmt "  change (%sznz_digits (word _ (S (S n))) (mk_zn2z_op_karatsuba (make_op n))) with\n" "@";
  fprintf fmt "    (xO (znz_digits (make_op n))).\n";
  fprintf fmt "  rewrite (fun x y => (Zpos_xO (%sznz_digits x y))).\n" "@";
  fprintf fmt "  rewrite inj_S; unfold Zsucc.\n";
  fprintf fmt "  rewrite Zplus_comm; rewrite Zpower_exp; auto with zarith.\n";
  fprintf fmt "  rewrite Zpower_exp_1.\n";
  fprintf fmt "  assert (tmp: forall x y z, x * (y * z) = y * (x * z));\n";
  fprintf fmt "   [intros; ring | rewrite tmp; clear tmp].\n";
  fprintf fmt "  apply Zmult_le_compat_l; auto with zarith.\n";
  fprintf fmt "  Qed.\n";
  end
  else
  fprintf fmt "  Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition of_N x :=\n";
  fprintf fmt "  match x with\n";
  fprintf fmt "  | BinNat.N0 => zero\n";
  fprintf fmt "  | Npos p => of_pos p\n";
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_of_N: forall x,\n";
  fprintf fmt "   [of_N x] = Z_of_N x.\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x.\n";
  fprintf fmt "  simpl of_N.\n";
  fprintf fmt "  unfold zero, w_0, to_Z; rewrite (spec_0 w0_spec); auto.\n";
  fprintf fmt " intros p; exact (spec_of_pos p).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt "  Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " (***************************************************************)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (*                          Shift                              *)\n";
  fprintf fmt " (*                                                             *)\n";
  fprintf fmt " (***************************************************************)\n\n";



 (* Head0 *)
  fprintf fmt " Definition head0 w := match w with\n";
  for i = 0 to size do
    fprintf fmt " | %s%i w=> reduce_%i (w%i_op.(znz_head0) w)\n"  c i i i;
  done;
  fprintf fmt " | %sn n w=> reduce_n n ((make_op n).(znz_head0) w)\n" c;
  fprintf fmt " end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_head00: forall x, [x] = 0 ->[head0 x] = Zpos (digits x).\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold head0; clear x.\n";
  for i = 0 to size do
    fprintf fmt "   intros x; rewrite spec_reduce_%i; exact (spec_head00 w%i_spec x).\n" i i;
  done;
  fprintf fmt " intros n x; rewrite spec_reduce_n; exact (spec_head00 (wn_spec n) x).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "  \n";

  fprintf fmt " Theorem spec_head0: forall x, 0 < [x] ->\n";
  fprintf fmt "   2 ^ (Zpos (digits x) - 1) <= 2 ^ [head0 x] * [x] < 2 ^ Zpos (digits x).\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F0: forall x, (x - 1) + 1 = x).\n";
  fprintf fmt "   intros; ring. \n";
  fprintf fmt " intros x; case x; unfold digits, head0; clear x.\n";
  for i = 0 to size do
    fprintf fmt " intros x Hx; rewrite spec_reduce_%i.\n" i;
    fprintf fmt " assert (F1:= spec_more_than_1_digit w%i_spec).\n" i;
    fprintf fmt " generalize (spec_head0 w%i_spec x Hx).\n" i;
    fprintf fmt " unfold base.\n";
    fprintf fmt " pattern (Zpos (znz_digits w%i_op)) at 1; \n" i;
    fprintf fmt " rewrite <- (fun x => (F0 (Zpos x))).\n";
    fprintf fmt " rewrite Zpower_exp; auto with zarith.\n";
    fprintf fmt " rewrite Zpower_exp_1; rewrite Z_div_mult; auto with zarith.\n";
  done;
  fprintf fmt " intros n x Hx; rewrite spec_reduce_n.\n";
  fprintf fmt " assert (F1:= spec_more_than_1_digit (wn_spec n)).\n";
  fprintf fmt " generalize (spec_head0 (wn_spec n) x Hx).\n";
  fprintf fmt " unfold base.\n";
  fprintf fmt " pattern (Zpos (znz_digits (make_op n))) at 1; \n";
  fprintf fmt " rewrite <- (fun x => (F0 (Zpos x))).\n";
  fprintf fmt " rewrite Zpower_exp; auto with zarith.\n";
  fprintf fmt " rewrite Zpower_exp_1; rewrite Z_div_mult; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


 (* Tail0 *)
  fprintf fmt " Definition tail0 w := match w with\n";
  for i = 0 to size do
    fprintf fmt " | %s%i w=> reduce_%i (w%i_op.(znz_tail0) w)\n"  c i i i;
  done;
  fprintf fmt " | %sn n w=> reduce_n n ((make_op n).(znz_tail0) w)\n" c;
  fprintf fmt " end.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_tail00: forall x, [x] = 0 ->[tail0 x] = Zpos (digits x).\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold tail0; clear x.\n";
  for i = 0 to size do
    fprintf fmt "   intros x; rewrite spec_reduce_%i; exact (spec_tail00 w%i_spec x).\n" i i;
  done;
  fprintf fmt " intros n x; rewrite spec_reduce_n; exact (spec_tail00 (wn_spec n) x).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "  \n";


  fprintf fmt " Theorem spec_tail0: forall x,\n";
  fprintf fmt "   0 < [x] -> exists y, 0 <= y /\\ [x] = (2 * y + 1) * 2 ^ [tail0 x].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; clear x; unfold tail0.\n";
  for i = 0 to size do
    fprintf fmt " intros x Hx; rewrite spec_reduce_%i; exact (spec_tail0 w%i_spec x Hx).\n" i  i;
  done;
  fprintf fmt " intros n x Hx; rewrite spec_reduce_n; exact (spec_tail0 (wn_spec n) x Hx).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  (* Number of digits *)
  fprintf fmt " Definition %sdigits x :=\n" c;
  fprintf fmt "  match x with\n";
  fprintf fmt "  | %s0 _ => %s0 w0_op.(znz_zdigits)\n" c c;
  for i = 1 to size do 
    fprintf fmt "  | %s%i _ => reduce_%i w%i_op.(znz_zdigits)\n" c i i i;
  done;
  fprintf fmt "  | %sn n _ => reduce_n n (make_op n).(znz_zdigits)\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_Ndigits: forall x, [Ndigits x] = Zpos (digits x).\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; clear x; unfold Ndigits, digits.\n";
  for i = 0 to size do
    fprintf fmt " intros _; try rewrite spec_reduce_%i; exact (spec_zdigits w%i_spec).\n" i i;
  done;
  fprintf fmt " intros n _; try rewrite spec_reduce_n; exact (spec_zdigits (wn_spec n)).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


 (* Shiftr *)
  for i = 0 to size do
    fprintf fmt " Definition shiftr%i n x := w%i_op.(znz_add_mul_div) (w%i_op.(znz_sub) w%i_op.(znz_zdigits) n) w%i_op.(znz_0) x.\n" i i i i i;
  done;
  fprintf fmt " Definition shiftrn n p x := (make_op n).(znz_add_mul_div) ((make_op n).(znz_sub) (make_op n).(znz_zdigits) p) (make_op n).(znz_0) x.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition shiftr := Eval lazy beta delta [same_level] in \n";
  fprintf fmt "     same_level _ (fun n x => %s0 (shiftr0 n x))\n" c;
  for i = 1 to size do
  fprintf fmt "           (fun n x => reduce_%i (shiftr%i n x))\n" i i;
  done;
  fprintf fmt "           (fun n p x => reduce_n n (shiftrn n p x)).\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_shiftr: forall n x,\n";
  fprintf fmt "  [n] <= [Ndigits x] -> [shiftr n x] = [x] / 2 ^ [n].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F0: forall x y, x - (x - y) = y).\n";
  fprintf fmt "   intros; ring.\n";
  fprintf fmt " assert (F2: forall x y z, 0 <= x -> 0 <= y -> x < z -> 0 <= x / 2 ^ y < z).\n";
  fprintf fmt "   intros x y z HH HH1 HH2.\n";
  fprintf fmt "   split; auto with zarith.\n";
  fprintf fmt "   apply Zle_lt_trans with (2 := HH2); auto with zarith.\n";
  fprintf fmt "   apply ZDivModAux.Zdiv_le_upper_bound; auto with zarith.\n";
  fprintf fmt "   pattern x at 1; replace x with (x * 2 ^ 0); auto with zarith.\n";
  fprintf fmt "   apply Zmult_le_compat_l; auto.\n";
  fprintf fmt "   apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "   rewrite Zpower_exp_0; ring.\n";
  fprintf fmt "  assert (F3: forall x y, 0 <= y -> y <= x -> 0 <= x - y < 2 ^ x).\n";
  fprintf fmt "    intros xx y HH HH1.\n";
  fprintf fmt "    split; auto with zarith.\n";
  fprintf fmt "    apply Zle_lt_trans with xx; auto with zarith.\n";
  fprintf fmt "    apply ZPowerAux.Zpower2_lt_lin; auto with zarith.\n";
  fprintf fmt "  assert (F4: forall ww ww1 ww2 \n";
  fprintf fmt "         (ww_op: znz_op ww) (ww1_op: znz_op ww1) (ww2_op: znz_op ww2)\n";
  fprintf fmt "           xx yy xx1 yy1,\n";
  fprintf fmt "  znz_to_Z ww2_op yy <= znz_to_Z ww1_op (znz_zdigits ww1_op) ->\n";
  fprintf fmt "  znz_to_Z ww1_op (znz_zdigits ww1_op) <= znz_to_Z ww_op (znz_zdigits ww_op) ->\n";
  fprintf fmt "  znz_spec ww_op -> znz_spec ww1_op -> znz_spec ww2_op ->\n";
  fprintf fmt "  znz_to_Z ww_op xx1 = znz_to_Z ww1_op xx ->\n";
  fprintf fmt "  znz_to_Z ww_op yy1 = znz_to_Z ww2_op yy ->\n";
  fprintf fmt "  znz_to_Z ww_op\n";
  fprintf fmt "  (znz_add_mul_div ww_op (znz_sub ww_op (znz_zdigits ww_op)  yy1)\n";
  fprintf fmt "     (znz_0 ww_op) xx1) = znz_to_Z ww1_op xx / 2 ^ znz_to_Z ww2_op yy).\n";
  fprintf fmt "  intros ww ww1 ww2 ww_op ww1_op ww2_op xx yy xx1 yy1 Hl Hl1 Hw Hw1 Hw2 Hx Hy.\n";
  fprintf fmt "     case (spec_to_Z Hw xx1); auto with zarith; intros HH1 HH2.\n";
  fprintf fmt "     case (spec_to_Z Hw yy1); auto with zarith; intros HH3 HH4.\n";
  fprintf fmt "     rewrite <- Hx.\n";
  fprintf fmt "     rewrite <- Hy.\n";
  fprintf fmt "     generalize (spec_add_mul_div Hw\n";
  fprintf fmt "                  (znz_0 ww_op) xx1\n";
  fprintf fmt "                  (znz_sub ww_op (znz_zdigits ww_op) \n";
  fprintf fmt "                    yy1)\n";
  fprintf fmt "                ).\n";
  fprintf fmt "     rewrite (spec_0 Hw).\n";
  fprintf fmt "     rewrite Zmult_0_l; rewrite Zplus_0_l.\n";
  fprintf fmt "     rewrite (ZnZ.spec_sub Hw).\n";
  fprintf fmt "     rewrite Zmod_def_small; auto with zarith.\n";
  fprintf fmt "     rewrite (spec_zdigits Hw).\n";
  fprintf fmt "     rewrite F0.\n";
  fprintf fmt "     rewrite Zmod_def_small; auto with zarith.\n";
  fprintf fmt "     unfold base; rewrite (spec_zdigits Hw) in Hl1 |- *;\n";
  fprintf fmt "      auto with zarith.\n";
  fprintf fmt "  assert (F5: forall n m, (n <= m)%snat ->\n" "%";
  fprintf fmt "     Zpos (znz_digits (make_op n)) <= Zpos (znz_digits (make_op m))).\n";
  fprintf fmt "    intros n m HH; elim HH; clear m HH; auto with zarith.\n";
  fprintf fmt "    intros m HH Hrec; apply Zle_trans with (1 := Hrec).\n";
  fprintf fmt "    rewrite make_op_S.\n";
  fprintf fmt "    match goal with |- Zpos ?Y <= ?X => change X with (Zpos (xO Y)) end.\n";
  fprintf fmt "    rewrite Zpos_xO.\n";
  fprintf fmt "    assert (0 <= Zpos (znz_digits (make_op n))); auto with zarith.\n";
  fprintf fmt "  assert (F6: forall n, Zpos (znz_digits w%i_op) <= Zpos (znz_digits (make_op n))).\n" size;
  fprintf fmt "    intros n ; apply Zle_trans with (Zpos (znz_digits (make_op 0))).\n";
  fprintf fmt "    change (znz_digits (make_op 0)) with (xO (znz_digits w%i_op)).\n" size;
  fprintf fmt "    rewrite Zpos_xO.\n";
  fprintf fmt "    assert (0 <= Zpos (znz_digits w%i_op)); auto with zarith.\n" size;
  fprintf fmt "    apply F5; auto with arith.\n";
  fprintf fmt "  intros x; case x; clear x; unfold shiftr, same_level.\n";
  for i = 0 to size do
    fprintf fmt "    intros x y; case y; clear y.\n";
    for j = 0 to i - 1 do
      fprintf fmt "     intros y; unfold shiftr%i, Ndigits.\n" i;
      fprintf fmt "       repeat rewrite spec_reduce_%i; repeat rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i j;
      fprintf fmt "       apply F4 with (3:=w%i_spec)(4:=w%i_spec)(5:=w%i_spec); auto with zarith.\n" i j i;
      fprintf fmt "       rewrite (spec_zdigits w%i_spec).\n" i;
      fprintf fmt "       rewrite (spec_zdigits w%i_spec).\n" j;
      fprintf fmt "       change (znz_digits w%i_op) with %s.\n" i (genxO (i - j) (" (znz_digits w"^(string_of_int j)^"_op)"));
      fprintf fmt "       repeat rewrite (fun x => Zpos_xO (xO x)).\n";
      fprintf fmt "       repeat rewrite (fun x y => Zpos_xO (%sznz_digits x y)).\n" "@";
      fprintf fmt "       assert (0 <= Zpos (znz_digits w%i_op)); auto with zarith.\n" j;
      fprintf fmt "       try (apply sym_equal; exact (spec_extend%in%i y)).\n" j i;
     
    done;
    fprintf fmt "     intros y; unfold shiftr%i, Ndigits.\n" i;
    fprintf fmt "     repeat rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i;
    fprintf fmt "       apply F4 with (3:=w%i_spec)(4:=w%i_spec)(5:=w%i_spec); auto with zarith.\n" i i i;
    for j = i + 1 to size do
      fprintf fmt "     intros y; unfold shiftr%i, Ndigits.\n" j;
      fprintf fmt "       repeat rewrite spec_reduce_%i; repeat rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i j;
      fprintf fmt "       apply F4 with (3:=w%i_spec)(4:=w%i_spec)(5:=w%i_spec); auto with zarith.\n" j j i;
      fprintf fmt "       try (apply sym_equal; exact (spec_extend%in%i x)).\n" i j;
    done;
    if i == size then
      begin
        fprintf fmt "     intros m y; unfold shiftrn, Ndigits.\n";
        fprintf fmt "       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.\n";
        fprintf fmt "       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w%i_spec); auto with zarith.\n" size;
        fprintf fmt "       try (apply sym_equal; exact (spec_extend%in m x)).\n" size;

      end
    else 
      begin
       fprintf fmt "     intros m y; unfold shiftrn, Ndigits.\n";
       fprintf fmt "       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.\n";
       fprintf fmt "       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w%i_spec); auto with zarith.\n" i;
       fprintf fmt "       change ([Nn m (extend%i m (extend%i %i x))] = [N%i x]).\n" size i (size - i - 1) i;
       fprintf fmt "       rewrite <- (spec_extend%in m); rewrite <- spec_extend%in%i; auto.\n" size i size;
      end
  done;
  fprintf fmt "    intros n x y; case y; clear y;\n";
  fprintf fmt "     intros y; unfold shiftrn, Ndigits; try rewrite spec_reduce_n.\n";
  for i = 0 to size do
    fprintf fmt "     try rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i;
    fprintf fmt "       apply F4 with (3:=(wn_spec n))(4:=w%i_spec)(5:=wn_spec n); auto with zarith.\n" i;
    fprintf fmt "       rewrite (spec_zdigits w%i_spec).\n" i;
    fprintf fmt "       rewrite (spec_zdigits (wn_spec n)).\n";
    fprintf fmt "       apply Zle_trans with (2 := F6 n).\n";
    fprintf fmt "       change (znz_digits w%i_op) with %s.\n" size (genxO (size - i) ("(znz_digits w" ^ (string_of_int i) ^ "_op)"));
    fprintf fmt "       repeat rewrite (fun x => Zpos_xO (xO x)).\n";
    fprintf fmt "       repeat rewrite (fun x y => Zpos_xO (%sznz_digits x y)).\n" "@";
    fprintf fmt "       assert (H: 0 <= Zpos (znz_digits w%i_op)); auto with zarith.\n" i;
    if i == size then
      fprintf fmt "       change ([Nn n (extend%i n y)] = [N%i y]).\n" size i
    else
      fprintf fmt "       change ([Nn n (extend%i n (extend%i %i y))] = [N%i y]).\n" size i (size - i - 1) i;
      fprintf fmt "       rewrite <- (spec_extend%in n); auto.\n" size;
    if i <> size then
      fprintf fmt "       try (rewrite <- spec_extend%in%i; auto).\n" i size;
  done;
  fprintf fmt "     generalize y; clear y; intros m y.\n";
  fprintf fmt "     rewrite spec_reduce_n; unfold to_Z; intros H1.\n";
  fprintf fmt "       apply F4 with (3:=(wn_spec (Max.max n m)))(4:=wn_spec m)(5:=wn_spec n); auto with zarith.\n";
  fprintf fmt "     rewrite (spec_zdigits (wn_spec m)).\n";
  fprintf fmt "     rewrite (spec_zdigits (wn_spec (Max.max n m))).\n";
  fprintf fmt "     apply F5; auto with arith.\n";
  fprintf fmt "     exact (spec_cast_r n m y).\n";
  fprintf fmt "     exact (spec_cast_l n m x).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Definition safe_shiftr n x := \n";
  fprintf fmt "   match compare n (Ndigits x) with\n ";
  fprintf fmt "   |  Lt => shiftr n x \n";
  fprintf fmt "   | _ => %s0 w_0\n" c;
  fprintf fmt "   end.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_safe_shiftr: forall n x,\n";
  fprintf fmt "   [safe_shiftr n x] = [x] / 2 ^ [n].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n x; unfold safe_shiftr;\n";
  fprintf fmt "    generalize (spec_compare n (Ndigits x)); case compare; intros H.\n";
  fprintf fmt " apply trans_equal with (1 := spec_0 w0_spec).\n";
  fprintf fmt " apply sym_equal; apply ZDivModAux.Zdiv_lt_0; rewrite H.\n";
  fprintf fmt " rewrite spec_Ndigits; exact (spec_digits x).\n";
  fprintf fmt " rewrite <- spec_shiftr; auto with zarith.\n";
  fprintf fmt " apply trans_equal with (1 := spec_0 w0_spec).\n";
  fprintf fmt " apply sym_equal; apply ZDivModAux.Zdiv_lt_0.\n";
  fprintf fmt " rewrite spec_Ndigits in H; case (spec_digits x); intros H1 H2.\n";
  fprintf fmt " split; auto.\n";
  fprintf fmt " apply Zlt_le_trans with (1 := H2).\n";
  fprintf fmt " apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt "\n";

 (* Shiftl *)
  for i = 0 to size do
    fprintf fmt " Definition shiftl%i n x := w%i_op.(znz_add_mul_div) n x w%i_op.(znz_0).\n" i i i
  done;
  fprintf fmt " Definition shiftln n p x := (make_op n).(znz_add_mul_div) p x (make_op n).(znz_0).\n";
  fprintf fmt " Definition shiftl := Eval lazy beta delta [same_level] in\n";
  fprintf fmt "    same_level _ (fun n x => %s0 (shiftl0 n x))\n" c;
  for i = 1 to size do
  fprintf fmt "           (fun n x => reduce_%i (shiftl%i n x))\n" i i;
  done;
  fprintf fmt "           (fun n p x => reduce_n n (shiftln n p x)).\n";
  fprintf fmt "\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_shiftl: forall n x,\n";
  fprintf fmt "  [n] <= [head0 x] -> [shiftl n x] = [x] * 2 ^ [n].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " assert (F0: forall x y, x - (x - y) = y).\n";
  fprintf fmt "   intros; ring.\n";
  fprintf fmt " assert (F2: forall x y z, 0 <= x -> 0 <= y -> x < z -> 0 <= x / 2 ^ y < z).\n";
  fprintf fmt "   intros x y z HH HH1 HH2.\n";
  fprintf fmt "   split; auto with zarith.\n";
  fprintf fmt "   apply Zle_lt_trans with (2 := HH2); auto with zarith.\n";
  fprintf fmt "   apply ZDivModAux.Zdiv_le_upper_bound; auto with zarith.\n";
  fprintf fmt "   pattern x at 1; replace x with (x * 2 ^ 0); auto with zarith.\n";
  fprintf fmt "   apply Zmult_le_compat_l; auto.\n";
  fprintf fmt "   apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "   rewrite Zpower_exp_0; ring.\n";
  fprintf fmt "  assert (F3: forall x y, 0 <= y -> y <= x -> 0 <= x - y < 2 ^ x).\n";
  fprintf fmt "    intros xx y HH HH1.\n";
  fprintf fmt "    split; auto with zarith.\n";
  fprintf fmt "    apply Zle_lt_trans with xx; auto with zarith.\n";
  fprintf fmt "    apply ZPowerAux.Zpower2_lt_lin; auto with zarith.\n";
  fprintf fmt "  assert (F4: forall ww ww1 ww2 \n";
  fprintf fmt "         (ww_op: znz_op ww) (ww1_op: znz_op ww1) (ww2_op: znz_op ww2)\n";
  fprintf fmt "           xx yy xx1 yy1,\n";
  fprintf fmt "  znz_to_Z ww2_op yy <= znz_to_Z ww1_op (znz_head0 ww1_op xx) ->\n";
  fprintf fmt "  znz_to_Z ww1_op (znz_zdigits ww1_op) <= znz_to_Z ww_op (znz_zdigits ww_op) ->\n";
  fprintf fmt "  znz_spec ww_op -> znz_spec ww1_op -> znz_spec ww2_op ->\n";
  fprintf fmt "  znz_to_Z ww_op xx1 = znz_to_Z ww1_op xx ->\n";
  fprintf fmt "  znz_to_Z ww_op yy1 = znz_to_Z ww2_op yy ->\n";
  fprintf fmt "  znz_to_Z ww_op\n";
  fprintf fmt "  (znz_add_mul_div ww_op yy1\n";
  fprintf fmt "     xx1 (znz_0 ww_op)) = znz_to_Z ww1_op xx * 2 ^ znz_to_Z ww2_op yy).\n";
  fprintf fmt "  intros ww ww1 ww2 ww_op ww1_op ww2_op xx yy xx1 yy1 Hl Hl1 Hw Hw1 Hw2 Hx Hy.\n";
  fprintf fmt "     case (spec_to_Z Hw xx1); auto with zarith; intros HH1 HH2.\n";
  fprintf fmt "     case (spec_to_Z Hw yy1); auto with zarith; intros HH3 HH4.\n";
  fprintf fmt "     rewrite <- Hx.\n";
  fprintf fmt "     rewrite <- Hy.\n";
  fprintf fmt "     generalize (spec_add_mul_div Hw xx1 (znz_0 ww_op) yy1).\n";
  fprintf fmt "     rewrite (spec_0 Hw).\n";
  fprintf fmt "     assert (F1: znz_to_Z ww1_op (znz_head0 ww1_op xx) <= Zpos (znz_digits ww1_op)).\n";
  fprintf fmt "     case (Zle_lt_or_eq _ _ HH1); intros HH5.\n";
  fprintf fmt "     apply Zlt_le_weak.\n";
  fprintf fmt "     case (ZnZ.spec_head0 Hw1 xx).\n";
  fprintf fmt "       rewrite <- Hx; auto.\n";
  fprintf fmt "     intros _ Hu; unfold base in Hu.\n";
  fprintf fmt "     case (Zle_or_lt (Zpos (znz_digits ww1_op))\n";
  fprintf fmt "                     (znz_to_Z ww1_op (znz_head0 ww1_op xx))); auto; intros H1.\n";
  fprintf fmt "     absurd (2 ^  (Zpos (znz_digits ww1_op)) <= 2 ^ (znz_to_Z ww1_op (znz_head0 ww1_op xx))).\n";
  fprintf fmt "       apply Zlt_not_le.\n";
  fprintf fmt "       case (spec_to_Z Hw1 xx); intros HHx3 HHx4.\n";
  fprintf fmt "       rewrite <- (Zmult_1_r (2 ^ znz_to_Z ww1_op (znz_head0 ww1_op xx))).\n";
  fprintf fmt "       apply Zle_lt_trans with (2 := Hu).\n";
  fprintf fmt "       apply Zmult_le_compat_l; auto with zarith.\n";
  fprintf fmt "     apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "     rewrite (ZnZ.spec_head00 Hw1 xx); auto with zarith.\n";
  fprintf fmt "     rewrite ZDivModAux.Zdiv_0; auto with zarith.\n";
  fprintf fmt "     rewrite Zplus_0_r.\n";
  fprintf fmt "     case (Zle_lt_or_eq _ _ HH1); intros HH5.\n";
  fprintf fmt "     rewrite Zmod_def_small; auto with zarith.\n";
  fprintf fmt "     intros HH; apply HH.\n";
  fprintf fmt "     rewrite Hy; apply Zle_trans with (1:= Hl).\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw). \n";
  fprintf fmt "     apply Zle_trans with (2 := Hl1); auto.\n";
  fprintf fmt "     rewrite  (spec_zdigits Hw1); auto with zarith.\n";
  fprintf fmt "     split; auto with zarith .\n";
  fprintf fmt "     apply Zlt_le_trans with (base (znz_digits ww1_op)).\n";
  fprintf fmt "     rewrite Hx.\n";
  fprintf fmt "     case (ZnZ.spec_head0 Hw1 xx); auto.\n";
  fprintf fmt "       rewrite <- Hx; auto.\n";
  fprintf fmt "     intros _ Hu; rewrite Zmult_comm in Hu.\n";
  fprintf fmt "     apply Zle_lt_trans with (2 := Hu).\n";
  fprintf fmt "     apply Zmult_le_compat_l; auto with zarith.\n";
  fprintf fmt "     apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "     unfold base; apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "     split; auto with zarith.\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw); auto with zarith.\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw1); auto with zarith.\n";
  fprintf fmt "     rewrite <- HH5.\n";
  fprintf fmt "     rewrite Zmult_0_l.\n";
  fprintf fmt "     rewrite Zmod_def_small; auto with zarith.\n";
  fprintf fmt "     intros HH; apply HH.\n";
  fprintf fmt "     rewrite Hy; apply Zle_trans with (1 := Hl).\n";
  fprintf fmt "     rewrite (ZnZ.spec_head00 Hw1 xx); auto with zarith.\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw); auto with zarith.\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw1); auto with zarith.\n";
  fprintf fmt "     apply Zpower_lt_0; auto with zarith.\n";
  fprintf fmt "     assert (znz_to_Z ww_op yy1 <= Zpos (znz_digits ww_op)); auto with zarith.\n";
  fprintf fmt "     rewrite Hy; apply Zle_trans with (1 := Hl).\n";
  fprintf fmt "     apply Zle_trans with (1 := F1).\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw); auto with zarith.\n";
  fprintf fmt "     rewrite <- (spec_zdigits Hw1); auto with zarith.\n";
  fprintf fmt "  assert (F5: forall n m, (n <= m)%snat ->\n" "%";
  fprintf fmt "     Zpos (znz_digits (make_op n)) <= Zpos (znz_digits (make_op m))).\n";
  fprintf fmt "    intros n m HH; elim HH; clear m HH; auto with zarith.\n";
  fprintf fmt "    intros m HH Hrec; apply Zle_trans with (1 := Hrec).\n";
  fprintf fmt "    rewrite make_op_S.\n";
  fprintf fmt "    match goal with |- Zpos ?Y <= ?X => change X with (Zpos (xO Y)) end.\n";
  fprintf fmt "    rewrite Zpos_xO.\n";
  fprintf fmt "    assert (0 <= Zpos (znz_digits (make_op n))); auto with zarith.\n";
  fprintf fmt "  assert (F6: forall n, Zpos (znz_digits w%i_op) <= Zpos (znz_digits (make_op n))).\n" size;
  fprintf fmt "    intros n ; apply Zle_trans with (Zpos (znz_digits (make_op 0))).\n";
  fprintf fmt "    change (znz_digits (make_op 0)) with (xO (znz_digits w%i_op)).\n" size;
  fprintf fmt "    rewrite Zpos_xO.\n";
  fprintf fmt "    assert (0 <= Zpos (znz_digits w%i_op)); auto with zarith.\n" size;
  fprintf fmt "    apply F5; auto with arith.\n";
  fprintf fmt "  intros x; case x; clear x; unfold shiftl, same_level.\n";
  for i = 0 to size do
    fprintf fmt "    intros x y; case y; clear y.\n";
    for j = 0 to i - 1 do
      fprintf fmt "     intros y; unfold shiftl%i, head0.\n" i;
      fprintf fmt "       repeat rewrite spec_reduce_%i; repeat rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i j;
      fprintf fmt "       apply F4 with (3:=w%i_spec)(4:=w%i_spec)(5:=w%i_spec); auto with zarith.\n" i j i;
      fprintf fmt "       rewrite (spec_zdigits w%i_spec).\n" i;
      fprintf fmt "       rewrite (spec_zdigits w%i_spec).\n" j;
      fprintf fmt "       change (znz_digits w%i_op) with %s.\n" i (genxO (i - j) (" (znz_digits w"^(string_of_int j)^"_op)"));
      fprintf fmt "       repeat rewrite (fun x => Zpos_xO (xO x)).\n";
      fprintf fmt "       repeat rewrite (fun x y => Zpos_xO (%sznz_digits x y)).\n" "@";
      fprintf fmt "       assert (0 <= Zpos (znz_digits w%i_op)); auto with zarith.\n" j;
      fprintf fmt "       try (apply sym_equal; exact (spec_extend%in%i y)).\n" j i;
     
    done;
    fprintf fmt "     intros y; unfold shiftl%i, head0.\n" i;
    fprintf fmt "     repeat rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i;
    fprintf fmt "       apply F4 with (3:=w%i_spec)(4:=w%i_spec)(5:=w%i_spec); auto with zarith.\n" i i i;
    for j = i + 1 to size do
      fprintf fmt "     intros y; unfold shiftl%i, head0.\n" j;
      fprintf fmt "       repeat rewrite spec_reduce_%i; repeat rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i j;
      fprintf fmt "       apply F4 with (3:=w%i_spec)(4:=w%i_spec)(5:=w%i_spec); auto with zarith.\n" j j i;
      fprintf fmt "       try (apply sym_equal; exact (spec_extend%in%i x)).\n" i j;
    done;
    if i == size then
      begin
        fprintf fmt "     intros m y; unfold shiftln, head0.\n";
        fprintf fmt "       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.\n";
        fprintf fmt "       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w%i_spec); auto with zarith.\n" size;
        fprintf fmt "       try (apply sym_equal; exact (spec_extend%in m x)).\n" size;

      end
    else 
      begin
       fprintf fmt "     intros m y; unfold shiftln, head0.\n";
       fprintf fmt "       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.\n";
       fprintf fmt "       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w%i_spec); auto with zarith.\n" i;
       fprintf fmt "       change ([Nn m (extend%i m (extend%i %i x))] = [N%i x]).\n" size i (size - i - 1) i;
       fprintf fmt "       rewrite <- (spec_extend%in m); rewrite <- spec_extend%in%i; auto.\n" size i size;
      end
  done;
  fprintf fmt "    intros n x y; case y; clear y;\n";
  fprintf fmt "     intros y; unfold shiftln, head0; try rewrite spec_reduce_n.\n";
  for i = 0 to size do
    fprintf fmt "     try rewrite spec_reduce_%i; unfold to_Z; intros H1.\n" i;
    fprintf fmt "       apply F4 with (3:=(wn_spec n))(4:=w%i_spec)(5:=wn_spec n); auto with zarith.\n" i;
    fprintf fmt "       rewrite (spec_zdigits w%i_spec).\n" i;
    fprintf fmt "       rewrite (spec_zdigits (wn_spec n)).\n";
    fprintf fmt "       apply Zle_trans with (2 := F6 n).\n";
    fprintf fmt "       change (znz_digits w%i_op) with %s.\n" size (genxO (size - i) ("(znz_digits w" ^ (string_of_int i) ^ "_op)"));
    fprintf fmt "       repeat rewrite (fun x => Zpos_xO (xO x)).\n";
    fprintf fmt "       repeat rewrite (fun x y => Zpos_xO (%sznz_digits x y)).\n" "@";
    fprintf fmt "       assert (H: 0 <= Zpos (znz_digits w%i_op)); auto with zarith.\n" i;
    if i == size then
      fprintf fmt "       change ([Nn n (extend%i n y)] = [N%i y]).\n" size i
    else
      fprintf fmt "       change ([Nn n (extend%i n (extend%i %i y))] = [N%i y]).\n" size i (size - i - 1) i;
      fprintf fmt "       rewrite <- (spec_extend%in n); auto.\n" size;
    if i <> size then
      fprintf fmt "       try (rewrite <- spec_extend%in%i; auto).\n" i size;
  done;
  fprintf fmt "     generalize y; clear y; intros m y.\n";
  fprintf fmt "     repeat rewrite spec_reduce_n; unfold to_Z; intros H1.\n";
  fprintf fmt "       apply F4 with (3:=(wn_spec (Max.max n m)))(4:=wn_spec m)(5:=wn_spec n); auto with zarith.\n";
  fprintf fmt "     rewrite (spec_zdigits (wn_spec m)).\n";
  fprintf fmt "     rewrite (spec_zdigits (wn_spec (Max.max n m))).\n";
  fprintf fmt "     apply F5; auto with arith.\n";
  fprintf fmt "     exact (spec_cast_r n m y).\n";
  fprintf fmt "     exact (spec_cast_l n m x).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

 (* Double size *)
  fprintf fmt " Definition double_size w := match w with\n";
  for i = 0 to size-1 do
    fprintf fmt " | %s%i x => %s%i (WW (znz_0 w%i_op) x)\n" c i c (i + 1) i;
  done;
  fprintf fmt " | %s%i x => %sn 0 (WW (znz_0 w%i_op) x)\n" c size c size;
  fprintf fmt " | %sn n x => %sn (S n) (WW (znz_0 (make_op n)) x)\n" c c;
  fprintf fmt " end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_double_size_digits: \n";
  fprintf fmt "   forall x, digits (double_size x) = xO (digits x).\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold double_size, digits; clear x; auto.\n";
  fprintf fmt " intros n x; rewrite make_op_S; auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_double_size: forall x, [double_size x] = [x].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold double_size; clear x.\n";
  for i = 0 to size do
    fprintf fmt "   intros x; unfold to_Z, make_op; \n";
    fprintf fmt "     rewrite znz_to_Z_%i; rewrite (spec_0 w%i_spec); auto with zarith.\n" (i + 1) i;
  done;
  fprintf fmt "   intros n x; unfold to_Z;\n";
  fprintf fmt "     generalize (znz_to_Z_n n); simpl word.\n";
  fprintf fmt "     intros HH; rewrite HH; clear HH.\n";
  fprintf fmt "     generalize (spec_0 (wn_spec n)); simpl word.\n";
  fprintf fmt "     intros HH; rewrite HH; clear HH; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_double_size_head0: \n";
  fprintf fmt "   forall x, 2 * [head0 x] <= [head0 (double_size x)].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x.\n";
  fprintf fmt " assert (F1:= to_Z_pos (head0 x)).\n";
  fprintf fmt " assert (F2: 0 < Zpos (digits x)).\n";
  fprintf fmt "   red; auto.\n";
  fprintf fmt " case (Zle_lt_or_eq _ _ (to_Z_pos x)); intros HH.\n";
  fprintf fmt " generalize HH; rewrite <- (spec_double_size x); intros HH1.\n";
  fprintf fmt " case (spec_head0 x HH); intros _ HH2.\n";
  fprintf fmt " case (spec_head0 _ HH1).\n";
  fprintf fmt " rewrite (spec_double_size x); rewrite (spec_double_size_digits x).\n";
  fprintf fmt " intros HH3 _.\n";
  fprintf fmt " case (Zle_or_lt ([head0 (double_size x)]) (2 * [head0 x])); auto; intros HH4.\n";
  fprintf fmt " absurd (2 ^ (2 * [head0 x] )* [x] < 2 ^ [head0 (double_size x)] * [x]); auto.\n";
  fprintf fmt " apply Zle_not_lt.\n";
  fprintf fmt " apply Zmult_le_compat_r; auto with zarith.\n";
  fprintf fmt " apply Zpower_le_monotone; auto; auto with zarith.\n";
  fprintf fmt " generalize (to_Z_pos (head0 (double_size x))); auto with zarith.\n";
  fprintf fmt " assert (HH5: 2 ^[head0 x] <= 2 ^(Zpos (digits x) - 1)).\n";
  fprintf fmt "   case (Zle_lt_or_eq 1 [x]); auto with zarith; intros HH5.\n";
  fprintf fmt "   apply Zmult_le_reg_r with (2 ^ 1); auto with zarith.\n";
  fprintf fmt "   rewrite <- (fun x y z => Zpower_exp x (y - z)); auto with zarith.\n";
  fprintf fmt "   assert (tmp: forall x, x - 1 + 1 = x); [intros; ring | rewrite tmp; clear tmp].\n";
  fprintf fmt "   apply Zle_trans with (2 := Zlt_le_weak _ _ HH2).\n";
  fprintf fmt "   apply Zmult_le_compat_l; auto with zarith.\n";
  fprintf fmt "   rewrite Zpower_exp_1; auto with zarith.\n";
  fprintf fmt "   apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "   split; auto with zarith. \n";
  fprintf fmt "   case (Zle_or_lt (Zpos (digits x)) [head0 x]); auto with zarith; intros HH6.\n";
  fprintf fmt "   absurd (2 ^ Zpos (digits x) <= 2 ^ [head0 x] * [x]); auto with zarith.\n";
  fprintf fmt "   rewrite <- HH5; rewrite Zmult_1_r.\n";
  fprintf fmt "   apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt " rewrite (Zmult_comm 2).\n";
  fprintf fmt " rewrite Zpower_mult; auto with zarith.\n";
  fprintf fmt " rewrite Zpower_2.\n";
  fprintf fmt " apply Zlt_le_trans with (2 := HH3).\n";
  fprintf fmt " rewrite <- Zmult_assoc.\n";
  fprintf fmt " replace (Zpos (xO (digits x)) - 1) with\n";
  fprintf fmt "   ((Zpos (digits x) - 1) + (Zpos (digits x))).\n";
  fprintf fmt " rewrite Zpower_exp; auto with zarith.\n";
  fprintf fmt " apply Zmult_lt_compat; auto with zarith.\n";
  fprintf fmt " split; auto with zarith.\n";
  fprintf fmt " apply Zmult_lt_0_compat; auto with zarith.\n";
  fprintf fmt " rewrite Zpos_xO; ring.\n";
  fprintf fmt " apply Zlt_le_weak; auto.\n";
  fprintf fmt " repeat rewrite spec_head00; auto.\n";
  fprintf fmt " rewrite spec_double_size_digits.\n";
  fprintf fmt " rewrite Zpos_xO; auto with zarith.\n";
  fprintf fmt " rewrite spec_double_size; auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_double_size_head0_pos: \n";
  fprintf fmt "   forall x, 0 < [head0 (double_size x)].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x.\n";
  fprintf fmt " assert (F: 0 < Zpos (digits x)).\n";
  fprintf fmt "  red; auto.\n";
  fprintf fmt " case (Zle_lt_or_eq _ _ (to_Z_pos (head0 (double_size x)))); auto; intros F0.\n";
  fprintf fmt " case (Zle_lt_or_eq _ _ (to_Z_pos (head0 x))); intros F1.\n";
  fprintf fmt "   apply Zlt_le_trans with (2 := (spec_double_size_head0 x)); auto with zarith.\n";
  fprintf fmt " case (Zle_lt_or_eq _ _ (to_Z_pos x)); intros F3.\n";
  fprintf fmt " generalize F3; rewrite <- (spec_double_size x); intros F4.\n";
  fprintf fmt " absurd (2 ^ (Zpos (xO (digits x)) - 1) < 2 ^ (Zpos (digits x))).\n";
  fprintf fmt "   apply Zle_not_lt.\n";
  fprintf fmt "   apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt "   split; auto with zarith.\n";
  fprintf fmt "   rewrite Zpos_xO; auto with zarith.\n";
  fprintf fmt " case (spec_head0 x F3).\n";
  fprintf fmt " rewrite <- F1; rewrite Zpower_exp_0; rewrite Zmult_1_l; intros _ HH.\n";
  fprintf fmt " apply Zle_lt_trans with (2 := HH).\n";
  fprintf fmt " case (spec_head0 _ F4).\n";
  fprintf fmt " rewrite (spec_double_size x); rewrite (spec_double_size_digits x).\n";
  fprintf fmt " rewrite <- F0; rewrite Zpower_exp_0; rewrite Zmult_1_l; auto.\n";
  fprintf fmt " generalize F1; rewrite (spec_head00 _ (sym_equal F3)); auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


 (* Safe shiftl *)

  fprintf fmt " Definition safe_shiftl_aux_body cont n x :=\n";
  fprintf fmt "   match compare n (head0 x)  with\n";
  fprintf fmt "      Gt => cont n (double_size x)\n";
  fprintf fmt "   |  _ => shiftl n x\n";
  fprintf fmt "   end.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_safe_shift_aux_body: forall n p x cont,\n";
  fprintf fmt "       2^ Zpos p  <=  [head0 x]  ->\n";
  fprintf fmt "      (forall x, 2 ^ (Zpos p + 1) <= [head0 x]->\n";
  fprintf fmt "         [cont n x] = [x] * 2 ^ [n]) ->\n";
  fprintf fmt "      [safe_shiftl_aux_body cont n x] = [x] * 2 ^ [n].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n p x cont H1 H2; unfold safe_shiftl_aux_body.\n";
  fprintf fmt " generalize (spec_compare n (head0 x)); case compare; intros H.\n";
  fprintf fmt "  apply spec_shiftl; auto with zarith.\n";
  fprintf fmt "  apply spec_shiftl; auto with zarith.\n";
  fprintf fmt " rewrite H2.\n";
  fprintf fmt " rewrite spec_double_size; auto.\n";
  fprintf fmt " rewrite Zplus_comm; rewrite Zpower_exp; auto with zarith.\n";
  fprintf fmt " apply Zle_trans with (2 := spec_double_size_head0 x).\n";
  fprintf fmt " rewrite Zpower_exp_1; apply Zmult_le_compat_l; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  fprintf fmt " Fixpoint safe_shiftl_aux p cont n x  {struct p} :=\n";
  fprintf fmt "   safe_shiftl_aux_body \n";
  fprintf fmt "       (fun n x => match p with\n";
  fprintf fmt "        | xH => cont n x\n";
  fprintf fmt "        | xO p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x\n";
  fprintf fmt "        | xI p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x\n";
  fprintf fmt "        end) n x.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_safe_shift_aux: forall p q n x cont,\n";
  fprintf fmt "    2 ^ (Zpos q) <= [head0 x] ->\n";
  fprintf fmt "      (forall x, 2 ^ (Zpos p + Zpos q) <= [head0 x] ->\n";
  fprintf fmt "         [cont n x] = [x] * 2 ^ [n]) ->      \n";
  fprintf fmt "      [safe_shiftl_aux p cont n x] = [x] * 2 ^ [n].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros p; elim p; unfold safe_shiftl_aux; fold safe_shiftl_aux; clear p.\n";
  fprintf fmt " intros p Hrec q n x cont H1 H2.\n";
  fprintf fmt " apply spec_safe_shift_aux_body with (q); auto.\n";
  fprintf fmt " intros x1 H3; apply Hrec with (q + 1)%spositive; auto.\n" "%";
  fprintf fmt " intros x2 H4; apply Hrec with (p + q + 1)%spositive; auto.\n" "%";
  fprintf fmt " rewrite <- Pplus_assoc.\n";
  fprintf fmt " rewrite Zpos_plus_distr; auto.\n";
  fprintf fmt " intros x3 H5; apply H2.\n";
  fprintf fmt " rewrite Zpos_xI.\n";
  fprintf fmt " replace (2 * Zpos p + 1 + Zpos q) with (Zpos p + Zpos (p + q + 1));\n";
  fprintf fmt "   auto.\n";
  fprintf fmt " repeat rewrite Zpos_plus_distr; ring.\n";
  fprintf fmt " intros p Hrec q n x cont H1 H2.\n";
  fprintf fmt " apply spec_safe_shift_aux_body with (q); auto.\n";
  fprintf fmt " intros x1 H3; apply Hrec with (q); auto.\n";
  fprintf fmt " apply Zle_trans with (2 := H3); auto with zarith.\n";
  fprintf fmt " apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt " intros x2 H4; apply Hrec with (p + q)%spositive; auto.\n" "%";
  fprintf fmt " intros x3 H5; apply H2.\n";
  fprintf fmt " rewrite (Zpos_xO p).\n";
  fprintf fmt " replace (2 * Zpos p + Zpos q) with (Zpos p + Zpos (p + q));\n";
  fprintf fmt "   auto.\n";
  fprintf fmt " repeat rewrite Zpos_plus_distr; ring.\n";
  fprintf fmt " intros q n x cont H1 H2.\n";
  fprintf fmt " apply spec_safe_shift_aux_body with (q); auto.\n";
  fprintf fmt " rewrite Zplus_comm; auto.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";


  fprintf fmt " Definition safe_shiftl n x :=\n";
  fprintf fmt "  safe_shiftl_aux_body\n";
  fprintf fmt "   (safe_shiftl_aux_body\n";
  fprintf fmt "    (safe_shiftl_aux (digits n) shiftl)) n x.\n";
  fprintf fmt "\n";

  fprintf fmt " Theorem spec_safe_shift: forall n x,\n";
  fprintf fmt "   [safe_shiftl n x] = [x] * 2 ^ [n].\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros n x; unfold safe_shiftl, safe_shiftl_aux_body.\n";
  fprintf fmt " generalize (spec_compare n (head0 x)); case compare; intros H.\n";
  fprintf fmt "  apply spec_shiftl; auto with zarith.\n";
  fprintf fmt "  apply spec_shiftl; auto with zarith.\n";
  fprintf fmt " rewrite <- (spec_double_size x).\n";
  fprintf fmt " generalize (spec_compare n (head0 (double_size x))); case compare; intros H1.\n";
  fprintf fmt "  apply spec_shiftl; auto with zarith.\n";
  fprintf fmt "  apply spec_shiftl; auto with zarith.\n";
  fprintf fmt " rewrite <- (spec_double_size (double_size x)).\n";
  fprintf fmt " apply spec_safe_shift_aux with 1%spositive.\n" "%";
  fprintf fmt " apply Zle_trans with (2 := spec_double_size_head0 (double_size x)).\n";
  fprintf fmt " replace (2 ^ 1) with (2 * 1).\n";
  fprintf fmt " apply Zmult_le_compat_l; auto with zarith.\n";
  fprintf fmt " generalize (spec_double_size_head0_pos x); auto with zarith.\n";
  fprintf fmt " rewrite Zpower_exp_1; ring.\n";
  fprintf fmt " intros x1 H2; apply spec_shiftl.\n";
  fprintf fmt " apply Zle_trans with (2 := H2).\n";
  fprintf fmt " apply Zle_trans with (2 ^ Zpos (digits n)); auto with zarith.\n";
  fprintf fmt " case (spec_digits n); auto with zarith.\n";
  fprintf fmt " apply Zpower_le_monotone; auto with zarith.\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";

  (* even *)
  fprintf fmt " Definition is_even x :=\n";
  fprintf fmt "  match x with\n";
  for i = 0 to size do
    fprintf fmt "  | %s%i wx => w%i_op.(znz_is_even) wx\n" c i i
  done;
  fprintf fmt "  | %sn n wx => (make_op n).(znz_is_even) wx\n" c;
  fprintf fmt "  end.\n";
  fprintf fmt "\n";


  fprintf fmt " Theorem spec_is_even: forall x,\n";
  fprintf fmt "   if is_even x then [x] mod 2 = 0 else [x] mod 2 = 1.\n";
  if gen_proof then
  begin
  fprintf fmt " Proof.\n";
  fprintf fmt " intros x; case x; unfold is_even, to_Z; clear x.\n";
  for i = 0 to size do
    fprintf fmt "   intros x; exact (spec_is_even w%i_spec x).\n" i;
  done;
  fprintf fmt "  intros n x; exact (spec_is_even (wn_spec n) x).\n";
  fprintf fmt " Qed.\n";
  end
  else
  fprintf fmt " Admitted.\n";
  fprintf fmt "\n";



  fprintf fmt "End Make.\n";
  fprintf fmt "\n";
  pp_print_flush fmt ()




let _ = print_Make ()


