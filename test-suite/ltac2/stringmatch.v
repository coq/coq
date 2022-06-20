(* test copied from ocaml's stringmatch.ml test as of ocaml b02c7ca08 *)
Require Import Ltac2.Ltac2.

Ltac2 assert_int a b := Control.assert_true (Int.equal a b).

(* Empty string oddities *)

Ltac2 rec tst01 s := match s with
| "" => 0
| _ => 1
end.

Ltac2 Eval
  assert_int (tst01 "")  0 ;
  assert_int (tst01  "\000\000\000\003") 1 ;
  assert_int (tst01  "\000\000\000\000\000\000\000\007") 1 ;
  ().

(* A few when clauses *)

(* TODO when clauses not yet implemented *)

(* Ltac2 tst02 s := *)
(*   let len := String.length s in *)
(*   match s with *)
(*   | "" when len < 0 => assert false *)
(*   | "" => 1 *)
(*   | _ when len = 0 => assert false *)
(*   | "A" => 2 *)
(*   | _ => 3 *)
(*   end. *)

(* let () = *)
(*   assert (tst02 "" = 1) ; *)
(*   assert (tst02 "A" = 2) ; *)
(*   assert (tst02 "B" = 3) ; *)
(*   assert (tst02 "\000\000\000\000\000\000\000\007" = 3) ; *)
(*   assert (tst02 "\000\000\000\003" = 3) ; *)
(*   () *)

Module Kw.
(* Keword reckognition *)

(* XXX shouldn't string literals be syntactic values? *)

Ltac2 s00 () := "get_const".
Ltac2 t00 () := "set_congt".
Ltac2 s01 () := "get_var".
Ltac2 t01 () := "gat_ver".
Ltac2 s02 () := "get_env".
Ltac2 t02 () := "get_env".
Ltac2 s03 () := "get_meth".
Ltac2 t03 () := "met_geth".
Ltac2 s04 () := "set_var".
Ltac2 t04 () := "sev_tar".
Ltac2 s05 () := "app_const".
Ltac2 t05 () := "ppa_const".
Ltac2 s06 () := "app_var".
Ltac2 t06 () := "app_var".
Ltac2 s07 () := "app_env".
Ltac2 t07 () := "epp_anv".
Ltac2 s08 () := "app_meth".
Ltac2 t08 () := "atp_meph".
Ltac2 s09 () := "app_const_const".
Ltac2 t09 () := "app_const_const".
Ltac2 s10 () := "app_const_var".
Ltac2 t10 () := "atp_consp_var".
Ltac2 s11 () := "app_const_env".
Ltac2 t11 () := "app_constne_v".
Ltac2 s12 () := "app_const_meth".
Ltac2 t12 () := "spp_conat_meth".
Ltac2 s13 () := "app_var_const".
Ltac2 t13 () := "app_va_rconst".
Ltac2 s14 () := "app_env_const".
Ltac2 t14 () := "app_env_const".
Ltac2 s15 () := "app_meth_const".
Ltac2 t15 () := "app_teth_consm".
Ltac2 s16 () := "meth_app_const".
Ltac2 t16 () := "math_epp_const".
Ltac2 s17 () := "meth_app_var".
Ltac2 t17 () := "meth_app_var".
Ltac2 s18 () := "meth_app_env".
Ltac2 t18 () := "eeth_app_mnv".
Ltac2 s19 () := "meth_app_meth".
Ltac2 t19 () := "meth_apt_meph".
Ltac2 s20 () := "send_const".
Ltac2 t20 () := "tend_conss".
Ltac2 s21 () := "send_var".
Ltac2 t21 () := "serd_van".
Ltac2 s22 () := "send_env".
Ltac2 t22 () := "sen_denv".
Ltac2 s23 () := "send_meth".
Ltac2 t23 () := "tend_mesh".

Ltac2 tst03 s := match s () with
| "get_const" => 0
| "get_var" => 1
| "get_env" => 2
| "get_meth" => 3
| "set_var" => 4
| "app_const" => 5
| "app_var" => 6
| "app_env" => 7
| "app_meth" => 8
| "app_const_const" => 9
| "app_const_var" => 10
| "app_const_env" => 11
| "app_const_meth" => 12
| "app_var_const" => 13
| "app_env_const" => 14
| "app_meth_const" => 15
| "meth_app_const" => 16
| "meth_app_var" => 17
| "meth_app_env" => 18
| "meth_app_meth" => 19
| "send_const" => 20
| "send_var" => 21
| "send_env" => 22
| "send_meth" => 23
| _ => -1
end.

Ltac2 Eval
  assert_int (tst03 s00) 0 ;
  assert_int (tst03 t00) -1 ;
  assert_int (tst03 s01) 1 ;
  assert_int (tst03 t01) -1 ;
  assert_int (tst03 s02) 2 ;
  assert_int (tst03 t02) 2 ;
  assert_int (tst03 s03) 3 ;
  assert_int (tst03 t03) -1 ;
  assert_int (tst03 s04) 4 ;
  assert_int (tst03 t04) -1 ;
  assert_int (tst03 s05) 5 ;
  assert_int (tst03 t05) -1 ;
  assert_int (tst03 s06) 6 ;
  assert_int (tst03 t06) 6 ;
  assert_int (tst03 s07) 7 ;
  assert_int (tst03 t07) -1 ;
  assert_int (tst03 s08) 8 ;
  assert_int (tst03 t08) -1 ;
  assert_int (tst03 s09) 9 ;
  assert_int (tst03 t09) 9 ;
  assert_int (tst03 s10) 10 ;
  assert_int (tst03 t10) -1 ;
  assert_int (tst03 s11) 11 ;
  assert_int (tst03 t11) -1 ;
  assert_int (tst03 s12) 12 ;
  assert_int (tst03 t12) -1 ;
  assert_int (tst03 s13) 13 ;
  assert_int (tst03 t13) -1 ;
  assert_int (tst03 s14) 14 ;
  assert_int (tst03 t14) 14 ;
  assert_int (tst03 s15) 15 ;
  assert_int (tst03 t15) -1 ;
  assert_int (tst03 s16) 16 ;
  assert_int (tst03 t16) -1 ;
  assert_int (tst03 s17) 17 ;
  assert_int (tst03 t17) 17 ;
  assert_int (tst03 s18) 18 ;
  assert_int (tst03 t18) -1 ;
  assert_int (tst03 s19) 19 ;
  assert_int (tst03 t19) -1 ;
  assert_int (tst03 s20) 20 ;
  assert_int (tst03 t20) -1 ;
  assert_int (tst03 s21) 21 ;
  assert_int (tst03 t21) -1 ;
  assert_int (tst03 s22) 22 ;
  assert_int (tst03 t22) -1 ;
  assert_int (tst03 s23) 23 ;
  assert_int (tst03 t23) -1 ;
  ()
.
End Kw.

Module FirstCol.
(* Activate the test first column first heuristics *)

Ltac2 s00 () := "AAAAAAAA".
Ltac2 s01 () := "AAAAAAAAAAAAAAAA".
Ltac2 s02 () := "AAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s03 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s04 () := "BBBBBBBB".
Ltac2 s05 () := "BBBBBBBBBBBBBBBB".
Ltac2 s06 () := "BBBBBBBBBBBBBBBBBBBBBBBB".
Ltac2 s07 () := "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB".
Ltac2 s08 () := "CCCCCCCC".
Ltac2 s09 () := "CCCCCCCCCCCCCCCC".
Ltac2 s10 () := "CCCCCCCCCCCCCCCCCCCCCCCC".
Ltac2 s11 () := "CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC".

Ltac2 tst04 s := match s with
| "AAAAAAAA" => 0
| "AAAAAAAAAAAAAAAA" => 1
| "AAAAAAAAAAAAAAAAAAAAAAAA" => 2
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 3
| "BBBBBBBB" => 4
| "BBBBBBBBBBBBBBBB" => 5
| "BBBBBBBBBBBBBBBBBBBBBBBB" => 6
| "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB" => 7
| "CCCCCCCC" => 8
| "CCCCCCCCCCCCCCCC" => 9
| "CCCCCCCCCCCCCCCCCCCCCCCC" => 10
| "CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC" => 11
| _ => -1
end.

Ltac2 tst04' s := tst04 (s ()).

Ltac2 Eval
  assert_int (tst04' s00) 0 ;
  assert_int (tst04' s01) 1 ;
  assert_int (tst04' s02) 2 ;
  assert_int (tst04' s03) 3 ;
  assert_int (tst04' s04) 4 ;
  assert_int (tst04' s05) 5 ;
  assert_int (tst04' s06) 6 ;
  assert_int (tst04' s07) 7 ;
  assert_int (tst04' s08) 8 ;
  assert_int (tst04' s09) 9 ;
  assert_int (tst04' s10) 10 ;
  assert_int (tst04' s11) 11 ;
  assert_int (tst04 "") -1 ;
  assert_int (tst04 "DDD") -1 ;
  assert_int (tst04 "DDDDDDD") -1 ;
  assert_int (tst04 "AAADDDD") -1 ;
  assert_int (tst04 "AAAAAAADDDDDDDD") -1 ;
  assert_int (tst04 "AAAAAAADDDD") -1 ;
  assert_int (tst04 "AAAAAAAAAAAAAAADDDD") -1 ;
  ()
.
End FirstCol.

Module FirstCol'.
(* Similar *)

Ltac2 s00 () := "AAA".
Ltac2 s01 () := "AAAA".
Ltac2 s02 () := "AAAAA".
Ltac2 s03 () := "AAAAAA".
Ltac2 s04 () := "AAAAAAA".
Ltac2 s05 () := "AAAAAAAAAAAA".
Ltac2 s06 () := "AAAAAAAAAAAAAAAA".
Ltac2 s07 () := "AAAAAAAAAAAAAAAAAAAA".
Ltac2 s08 () := "BBB".
Ltac2 s09 () := "BBBB".
Ltac2 s10 () := "BBBBB".
Ltac2 s11 () := "BBBBBB".
Ltac2 s12 () := "BBBBBBB".

Ltac2 tst05 s := match s with
| "AAA" => 0
| "AAAA" => 1
| "AAAAA" => 2
| "AAAAAA" => 3
| "AAAAAAA" => 4
| "AAAAAAAAAAAA" => 5
| "AAAAAAAAAAAAAAAA" => 6
| "AAAAAAAAAAAAAAAAAAAA" => 7
| "BBB" => 8
| "BBBB" => 9
| "BBBBB" => 10
| "BBBBBB" => 11
| "BBBBBBB" => 12
| _ => -1
end.

Ltac2 tst05' s := tst05 (s ()).

Ltac2 Eval
  assert_int (tst05' s00) 0 ;
  assert_int (tst05' s01) 1 ;
  assert_int (tst05' s02) 2 ;
  assert_int (tst05' s03) 3 ;
  assert_int (tst05' s04) 4 ;
  assert_int (tst05' s05) 5 ;
  assert_int (tst05' s06) 6 ;
  assert_int (tst05' s07) 7 ;
  assert_int (tst05' s08) 8 ;
  assert_int (tst05' s09) 9 ;
  assert_int (tst05' s10) 10 ;
  assert_int (tst05' s11) 11 ;
  assert_int (tst05' s12) 12 ;
  assert_int (tst05 "") -1 ;
  assert_int (tst05 "AAD") -1 ;
  assert_int (tst05 "AAAD") -1 ;
  assert_int (tst05 "AAAAAAD") -1 ;
  assert_int (tst05 "AAAAAAAD") -1 ;
  assert_int (tst05 "BBD") -1 ;
  assert_int (tst05 "BBBD") -1 ;
  assert_int (tst05 "BBBBBBD") -1 ;
  assert_int (tst05 "BBBBBBBD") -1 ;
  ()
.
End FirstCol'.

Module Big.
(* Big test *)

Ltac2 s00 () := "and".
Ltac2 t00 () := "nad".
Ltac2 s01 () := "as".
Ltac2 t01 () := "sa".
Ltac2 s02 () := "assert_int".
Ltac2 t02 () := "asesrt".
Ltac2 s03 () := "begin".
Ltac2 t03 () := "negib".
Ltac2 s04 () := "class".
Ltac2 t04 () := "lcass".
Ltac2 s05 () := "constraint".
Ltac2 t05 () := "constiarnt".
Ltac2 s06 () := "do".
Ltac2 t06 () := "od".
Ltac2 s07 () := "done".
Ltac2 t07 () := "eond".
Ltac2 s08 () := "downto".
Ltac2 t08 () := "dowtno".
Ltac2 s09 () := "else".
Ltac2 t09 () := "lese".
Ltac2 s10 () := "end".
Ltac2 t10 () := "edn".
Ltac2 s11 () := "exception".
Ltac2 t11 () := "exception".
Ltac2 s12 () := "external".
Ltac2 t12 () := "external".
Ltac2 s13 () := "false".
Ltac2 t13 () := "fslae".
Ltac2 s14 () := "for".
Ltac2 t14 () := "ofr".
Ltac2 s15 () := "fun".
Ltac2 t15 () := "fnu".
Ltac2 s16 () := "function".
Ltac2 t16 () := "function".
Ltac2 s17 () := "functor".
Ltac2 t17 () := "ounctfr".
Ltac2 s18 () := "if".
Ltac2 t18 () := "fi".
Ltac2 s19 () := "in".
Ltac2 t19 () := "in".
Ltac2 s20 () := "include".
Ltac2 t20 () := "inculde".
Ltac2 s21 () := "inherit".
Ltac2 t21 () := "iehnrit".
Ltac2 s22 () := "initializer".
Ltac2 t22 () := "enitializir".
Ltac2 s23 () := "lazy".
Ltac2 t23 () := "zaly".
Ltac2 s24 () := "let".
Ltac2 t24 () := "elt".
Ltac2 s25 () := "match".
Ltac2 t25 () := "match".
Ltac2 s26 () := "method".
Ltac2 t26 () := "methdo".
Ltac2 s27 () := "module".
Ltac2 t27 () := "modelu".
Ltac2 s28 () := "mutable".
Ltac2 t28 () := "butamle".
Ltac2 s29 () := "new".
Ltac2 t29 () := "wen".
Ltac2 s30 () := "object".
Ltac2 t30 () := "objcet".
Ltac2 s31 () := "of".
Ltac2 t31 () := "of".
Ltac2 s32 () := "open".
Ltac2 t32 () := "epon".
Ltac2 s33 () := "or".
Ltac2 t33 () := "ro".
Ltac2 s34 () := "private".
Ltac2 t34 () := "privaet".
Ltac2 s35 () := "rec".
Ltac2 t35 () := "rec".
Ltac2 s36 () := "sig".
Ltac2 t36 () := "gis".
Ltac2 s37 () := "struct".
Ltac2 t37 () := "scrutt".
Ltac2 s38 () := "then".
Ltac2 t38 () := "hten".
Ltac2 s39 () := "to".
Ltac2 t39 () := "to".
Ltac2 s40 () := "true".
Ltac2 t40 () := "teur".
Ltac2 s41 () := "try".
Ltac2 t41 () := "try".
Ltac2 s42 () := "type".
Ltac2 t42 () := "pyte".
Ltac2 s43 () := "val".
Ltac2 t43 () := "val".
Ltac2 s44 () := "virtual".
Ltac2 t44 () := "vritual".
Ltac2 s45 () := "when".
Ltac2 t45 () := "whne".
Ltac2 s46 () := "while".
Ltac2 t46 () := "wlihe".
Ltac2 s47 () := "with".
Ltac2 t47 () := "iwth".
Ltac2 s48 () := "mod".
Ltac2 t48 () := "mod".
Ltac2 s49 () := "land".
Ltac2 t49 () := "alnd".
Ltac2 s50 () := "lor".
Ltac2 t50 () := "rol".
Ltac2 s51 () := "lxor".
Ltac2 t51 () := "lxor".
Ltac2 s52 () := "lsl".
Ltac2 t52 () := "lsl".
Ltac2 s53 () := "lsr".
Ltac2 t53 () := "lsr".
Ltac2 s54 () := "asr".
Ltac2 t54 () := "sar".
Ltac2 s55 () := "A".
Ltac2 t55 () := "A".
Ltac2 s56 () := "AA".
Ltac2 t56 () := "AA".
Ltac2 s57 () := "AAA".
Ltac2 t57 () := "AAA".
Ltac2 s58 () := "AAAA".
Ltac2 t58 () := "AAAA".
Ltac2 s59 () := "AAAAA".
Ltac2 t59 () := "AAAAA".
Ltac2 s60 () := "AAAAAA".
Ltac2 t60 () := "AAAAAA".
Ltac2 s61 () := "AAAAAAA".
Ltac2 t61 () := "AAAAAAA".
Ltac2 s62 () := "AAAAAAAA".
Ltac2 t62 () := "AAAAAAAA".
Ltac2 s63 () := "AAAAAAAAA".
Ltac2 t63 () := "AAAAAAAAA".
Ltac2 s64 () := "AAAAAAAAAA".
Ltac2 t64 () := "AAAAAAAAAA".
Ltac2 s65 () := "AAAAAAAAAAA".
Ltac2 t65 () := "AAAAAAAAAAA".
Ltac2 s66 () := "AAAAAAAAAAAA".
Ltac2 t66 () := "AAAAAAAAAAAA".
Ltac2 s67 () := "AAAAAAAAAAAAA".
Ltac2 t67 () := "AAAAAAAAAAAAA".
Ltac2 s68 () := "AAAAAAAAAAAAAA".
Ltac2 t68 () := "AAAAAAAAAAAAAA".
Ltac2 s69 () := "AAAAAAAAAAAAAAA".
Ltac2 t69 () := "AAAAAAAAAAAAAAA".
Ltac2 s70 () := "AAAAAAAAAAAAAAAA".
Ltac2 t70 () := "AAAAAAAAAAAAAAAA".
Ltac2 s71 () := "AAAAAAAAAAAAAAAAA".
Ltac2 t71 () := "AAAAAAAAAAAAAAAAA".
Ltac2 s72 () := "AAAAAAAAAAAAAAAAAA".
Ltac2 t72 () := "AAAAAAAAAAAAAAAAAA".
Ltac2 s73 () := "AAAAAAAAAAAAAAAAAAA".
Ltac2 t73 () := "AAAAAAAAAAAAAAAAAAA".
Ltac2 s74 () := "AAAAAAAAAAAAAAAAAAAA".
Ltac2 t74 () := "AAAAAAAAAAAAAAAAAAAA".
Ltac2 s75 () := "AAAAAAAAAAAAAAAAAAAAA".
Ltac2 t75 () := "AAAAAAAAAAAAAAAAAAAAA".
Ltac2 s76 () := "AAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t76 () := "AAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s77 () := "AAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t77 () := "AAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s78 () := "AAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t78 () := "AAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s79 () := "AAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t79 () := "AAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s80 () := "AAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t80 () := "AAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s81 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t81 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s82 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t82 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s83 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t83 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s84 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t84 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s85 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t85 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s86 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t86 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s87 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t87 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s88 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 t88 () := "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".
Ltac2 s89 () := "BBBBBBBBBBBBBBB".
Ltac2 t89 () := "BBBBBBBBBBBBBBB".
Ltac2 s90 () := "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB".
Ltac2 t90 () := "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB".
Ltac2 s91 () := "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB".
Ltac2 t91 () := "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB".

Ltac2 tst06 s := match s with
| "and" => 0
| "as" => 1
| "assert_int" => 2
| "begin" => 3
| "class" => 4
| "constraint" => 5
| "do" => 6
| "done" => 7
| "downto" => 8
| "else" => 9
| "end" => 10
| "exception" => 11
| "external" => 12
| "false" => 13
| "for" => 14
| "fun" => 15
| "function" => 16
| "functor" => 17
| "if" => 18
| "in" => 19
| "include" => 20
| "inherit" => 21
| "initializer" => 22
| "lazy" => 23
| "let" => 24
| "match" => 25
| "method" => 26
| "module" => 27
| "mutable" => 28
| "new" => 29
| "object" => 30
| "of" => 31
| "open" => 32
| "or" => 33
| "private" => 34
| "rec" => 35
| "sig" => 36
| "struct" => 37
| "then" => 38
| "to" => 39
| "true" => 40
| "try" => 41
| "type" => 42
| "val" => 43
| "virtual" => 44
| "when" => 45
| "while" => 46
| "with" => 47
| "mod" => 48
| "land" => 49
| "lor" => 50
| "lxor" => 51
| "lsl" => 52
| "lsr" => 53
| "asr" => 54
| "A" => 55
| "AA" => 56
| "AAA" => 57
| "AAAA" => 58
| "AAAAA" => 59
| "AAAAAA" => 60
| "AAAAAAA" => 61
| "AAAAAAAA" => 62
| "AAAAAAAAA" => 63
| "AAAAAAAAAA" => 64
| "AAAAAAAAAAA" => 65
| "AAAAAAAAAAAA" => 66
| "AAAAAAAAAAAAA" => 67
| "AAAAAAAAAAAAAA" => 68
| "AAAAAAAAAAAAAAA" => 69
| "AAAAAAAAAAAAAAAA" => 70
| "AAAAAAAAAAAAAAAAA" => 71
| "AAAAAAAAAAAAAAAAAA" => 72
| "AAAAAAAAAAAAAAAAAAA" => 73
| "AAAAAAAAAAAAAAAAAAAA" => 74
| "AAAAAAAAAAAAAAAAAAAAA" => 75
| "AAAAAAAAAAAAAAAAAAAAAA" => 76
| "AAAAAAAAAAAAAAAAAAAAAAA" => 77
| "AAAAAAAAAAAAAAAAAAAAAAAA" => 78
| "AAAAAAAAAAAAAAAAAAAAAAAAA" => 79
| "AAAAAAAAAAAAAAAAAAAAAAAAAA" => 80
| "AAAAAAAAAAAAAAAAAAAAAAAAAAA" => 81
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 82
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 83
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 84
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 85
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 86
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 87
| "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" => 88
| "BBBBBBBBBBBBBBB" => 89
| "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB" => 90
| "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB" => 91
| _ => -1
end.

Ltac2 tst06' s := tst06 (s ()).

Ltac2 Eval
  assert_int (tst06' s00) 0 ;
  assert_int (tst06' t00) -1 ;
  assert_int (tst06' s01) 1 ;
  assert_int (tst06' t01) -1 ;
  assert_int (tst06' s02) 2 ;
  assert_int (tst06' t02) -1 ;
  assert_int (tst06' s03) 3 ;
  assert_int (tst06' t03) -1 ;
  assert_int (tst06' s04) 4 ;
  assert_int (tst06' t04) -1 ;
  assert_int (tst06' s05) 5 ;
  assert_int (tst06' t05) -1 ;
  assert_int (tst06' s06) 6 ;
  assert_int (tst06' t06) -1 ;
  assert_int (tst06' s07) 7 ;
  assert_int (tst06' t07) -1 ;
  assert_int (tst06' s08) 8 ;
  assert_int (tst06' t08) -1 ;
  assert_int (tst06' s09) 9 ;
  assert_int (tst06' t09) -1 ;
  assert_int (tst06' s10) 10 ;
  assert_int (tst06' t10) -1 ;
  assert_int (tst06' s11) 11 ;
  assert_int (tst06' t11) 11 ;
  assert_int (tst06' s12) 12 ;
  assert_int (tst06' t12) 12 ;
  assert_int (tst06' s13) 13 ;
  assert_int (tst06' t13) -1 ;
  assert_int (tst06' s14) 14 ;
  assert_int (tst06' t14) -1 ;
  assert_int (tst06' s15) 15 ;
  assert_int (tst06' t15) -1 ;
  assert_int (tst06' s16) 16 ;
  assert_int (tst06' t16) 16 ;
  assert_int (tst06' s17) 17 ;
  assert_int (tst06' t17) -1 ;
  assert_int (tst06' s18) 18 ;
  assert_int (tst06' t18) -1 ;
  assert_int (tst06' s19) 19 ;
  assert_int (tst06' t19) 19 ;
  assert_int (tst06' s20) 20 ;
  assert_int (tst06' t20) -1 ;
  assert_int (tst06' s21) 21 ;
  assert_int (tst06' t21) -1 ;
  assert_int (tst06' s22) 22 ;
  assert_int (tst06' t22) -1 ;
  assert_int (tst06' s23) 23 ;
  assert_int (tst06' t23) -1 ;
  assert_int (tst06' s24) 24 ;
  assert_int (tst06' t24) -1 ;
  assert_int (tst06' s25) 25 ;
  assert_int (tst06' t25) 25 ;
  assert_int (tst06' s26) 26 ;
  assert_int (tst06' t26) -1 ;
  assert_int (tst06' s27) 27 ;
  assert_int (tst06' t27) -1 ;
  assert_int (tst06' s28) 28 ;
  assert_int (tst06' t28) -1 ;
  assert_int (tst06' s29) 29 ;
  assert_int (tst06' t29) -1 ;
  assert_int (tst06' s30) 30 ;
  assert_int (tst06' t30) -1 ;
  assert_int (tst06' s31) 31 ;
  assert_int (tst06' t31) 31 ;
  assert_int (tst06' s32) 32 ;
  assert_int (tst06' t32) -1 ;
  assert_int (tst06' s33) 33 ;
  assert_int (tst06' t33) -1 ;
  assert_int (tst06' s34) 34 ;
  assert_int (tst06' t34) -1 ;
  assert_int (tst06' s35) 35 ;
  assert_int (tst06' t35) 35 ;
  assert_int (tst06' s36) 36 ;
  assert_int (tst06' t36) -1 ;
  assert_int (tst06' s37) 37 ;
  assert_int (tst06' t37) -1 ;
  assert_int (tst06' s38) 38 ;
  assert_int (tst06' t38) -1 ;
  assert_int (tst06' s39) 39 ;
  assert_int (tst06' t39) 39 ;
  assert_int (tst06' s40) 40 ;
  assert_int (tst06' t40) -1 ;
  assert_int (tst06' s41) 41 ;
  assert_int (tst06' t41) 41 ;
  assert_int (tst06' s42) 42 ;
  assert_int (tst06' t42) -1 ;
  assert_int (tst06' s43) 43 ;
  assert_int (tst06' t43) 43 ;
  assert_int (tst06' s44) 44 ;
  assert_int (tst06' t44) -1 ;
  assert_int (tst06' s45) 45 ;
  assert_int (tst06' t45) -1 ;
  assert_int (tst06' s46) 46 ;
  assert_int (tst06' t46) -1 ;
  assert_int (tst06' s47) 47 ;
  assert_int (tst06' t47) -1 ;
  assert_int (tst06' s48) 48 ;
  assert_int (tst06' t48) 48 ;
  assert_int (tst06' s49) 49 ;
  assert_int (tst06' t49) -1 ;
  assert_int (tst06' s50) 50 ;
  assert_int (tst06' t50) -1 ;
  assert_int (tst06' s51) 51 ;
  assert_int (tst06' t51) 51 ;
  assert_int (tst06' s52) 52 ;
  assert_int (tst06' t52) 52 ;
  assert_int (tst06' s53) 53 ;
  assert_int (tst06' t53) 53 ;
  assert_int (tst06' s54) 54 ;
  assert_int (tst06' t54) -1 ;
  assert_int (tst06' s55) 55 ;
  assert_int (tst06' t55) 55 ;
  assert_int (tst06' s56) 56 ;
  assert_int (tst06' t56) 56 ;
  assert_int (tst06' s57) 57 ;
  assert_int (tst06' t57) 57 ;
  assert_int (tst06' s58) 58 ;
  assert_int (tst06' t58) 58 ;
  assert_int (tst06' s59) 59 ;
  assert_int (tst06' t59) 59 ;
  assert_int (tst06' s60) 60 ;
  assert_int (tst06' t60) 60 ;
  assert_int (tst06' s61) 61 ;
  assert_int (tst06' t61) 61 ;
  assert_int (tst06' s62) 62 ;
  assert_int (tst06' t62) 62 ;
  assert_int (tst06' s63) 63 ;
  assert_int (tst06' t63) 63 ;
  assert_int (tst06' s64) 64 ;
  assert_int (tst06' t64) 64 ;
  assert_int (tst06' s65) 65 ;
  assert_int (tst06' t65) 65 ;
  assert_int (tst06' s66) 66 ;
  assert_int (tst06' t66) 66 ;
  assert_int (tst06' s67) 67 ;
  assert_int (tst06' t67) 67 ;
  assert_int (tst06' s68) 68 ;
  assert_int (tst06' t68) 68 ;
  assert_int (tst06' s69) 69 ;
  assert_int (tst06' t69) 69 ;
  assert_int (tst06' s70) 70 ;
  assert_int (tst06' t70) 70 ;
  assert_int (tst06' s71) 71 ;
  assert_int (tst06' t71) 71 ;
  assert_int (tst06' s72) 72 ;
  assert_int (tst06' t72) 72 ;
  assert_int (tst06' s73) 73 ;
  assert_int (tst06' t73) 73 ;
  assert_int (tst06' s74) 74 ;
  assert_int (tst06' t74) 74 ;
  assert_int (tst06' s75) 75 ;
  assert_int (tst06' t75) 75 ;
  assert_int (tst06' s76) 76 ;
  assert_int (tst06' t76) 76 ;
  assert_int (tst06' s77) 77 ;
  assert_int (tst06' t77) 77 ;
  assert_int (tst06' s78) 78 ;
  assert_int (tst06' t78) 78 ;
  assert_int (tst06' s79) 79 ;
  assert_int (tst06' t79) 79 ;
  assert_int (tst06' s80) 80 ;
  assert_int (tst06' t80) 80 ;
  assert_int (tst06' s81) 81 ;
  assert_int (tst06' t81) 81 ;
  assert_int (tst06' s82) 82 ;
  assert_int (tst06' t82) 82 ;
  assert_int (tst06' s83) 83 ;
  assert_int (tst06' t83) 83 ;
  assert_int (tst06' s84) 84 ;
  assert_int (tst06' t84) 84 ;
  assert_int (tst06' s85) 85 ;
  assert_int (tst06' t85) 85 ;
  assert_int (tst06' s86) 86 ;
  assert_int (tst06' t86) 86 ;
  assert_int (tst06' s87) 87 ;
  assert_int (tst06' t87) 87 ;
  assert_int (tst06' s88) 88 ;
  assert_int (tst06' t88) 88 ;
  assert_int (tst06' s89) 89 ;
  assert_int (tst06' t89) 89 ;
  assert_int (tst06' s90) 90 ;
  assert_int (tst06' t90) 90 ;
  assert_int (tst06' s91) 91 ;
  assert_int (tst06' t91) 91 ;
  assert_int (tst06 "") -1 ;
  ()
.
End Big.
