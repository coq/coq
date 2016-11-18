SET COQREGTESTING=Y

REM Bleeding edge
call MakeCoq_86git_abs_ocaml.bat
call MakeCoq_86git_installer.bat
call MakeCoq_86git_installer_32.bat
call MakeCoq_86git_abs_ocaml_gtksrc.bat

REM Current stable
call MakeCoq_85pl3_abs_ocaml.bat
call MakeCoq_85pl3_installer.bat
call MakeCoq_85pl3_installer_32.bat

REM Old but might still be used
call MakeCoq_85pl2_abs_ocaml.bat
call MakeCoq_84pl6_abs_ocaml.bat
