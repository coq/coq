; This script is used to build the Windows install program for Coq.

;NSIS Modern User Interface
;Written by Joost Verburg
;Modified by Julien Narboux

; The VERSION should be passed as an argument at compile time using :
;

!define MY_PRODUCT "Coq" ;Define your own software name here
!define EXE_PATH "..\..\bin\"

!include "MUI.nsh"

;--------------------------------
;Configuration

  Name "Coq"

  ;General
  OutFile "${OUTFILE}"

  ;Folder selection page
  InstallDir "$PROGRAMFILES\${MY_PRODUCT}"
  
  ;Remember install folder
  InstallDirRegKey HKCU "Software\${MY_PRODUCT}" ""

;Interface Configuration

;  !define MUI_HEADERIMAGE
;  !define MUI_HEADERIMAGE_BITMAP "coq_logo.bmp" ; optional
;  !define MUI_ABORTWARNING


;--------------------------------
;Modern UI Configuration

  !insertmacro MUI_PAGE_WELCOME
  !insertmacro MUI_PAGE_LICENSE "..\..\LICENSE"
  !insertmacro MUI_PAGE_COMPONENTS
  !insertmacro MUI_PAGE_DIRECTORY
  !insertmacro MUI_PAGE_INSTFILES
  !insertmacro MUI_PAGE_FINISH
  
  !insertmacro MUI_UNPAGE_WELCOME
  !insertmacro MUI_UNPAGE_CONFIRM
  !insertmacro MUI_UNPAGE_INSTFILES
  !insertmacro MUI_UNPAGE_FINISH  

;--------------------------------
;Languages
 
  !insertmacro MUI_LANGUAGE "English"
  
;--------------------------------
;Language Strings

  ;Description
  LangString DESC_1 ${LANG_ENGLISH} "This is the windows version of Coq."
  LangString DESC_2 ${LANG_ENGLISH} "This is CoqIde, an interactive development environment for Coq."
  LangString DESC_3 ${LANG_ENGLISH} "This will copy the GTK dlls in the installation directory (These files are needed by CoqIde)."

;--------------------------------
;Data
  
Function .onInit
  SetOutPath $TEMP
  File /oname=coq_splash.bmp "coq_splash.bmp"
	InitPluginsDir

  advsplash::show 1000 600 400 -1 $TEMP\coq_splash

  Pop $0 ; $0 has '1' if the user closed the splash screen early,
         ; '0' if everything closed normal, and '-1' if some error occured.

  Delete $TEMP\coq_splash.bmp
FunctionEnd


;--------------------------------
;Installer Sections

SetCompress off
;SetCompressor bzip2
; Comment out after debuging.

Section "Coq" Sec1

  ;ADD YOUR OWN STUFF HERE!

  SetOutPath "$INSTDIR\"

  FileOpen $0 $INSTDIR\Coq.bat w
  FileWrite $0 "@echo off$\r$\n"
  FileWrite $0 "set COQLIB=$INSTDIR\lib$\r$\n"
  FileWrite $0 "set COQBIN=$INSTDIR\bin$\r$\n"
  FileWrite $0 "set HOME=%HOMEPATH%$\r$\n"
  FileWrite $0 "bin\coqtop.opt.exe" 
  FileClose $0

  SetOutPath "$INSTDIR\bin"
  File /x coqide.* ${EXE_PATH}\*.exe
  File "coq.ico"

  SetOutPath "$INSTDIR\lib\theories"
  File /r ..\..\theories\*.vo
  SetOutPath "$INSTDIR\lib\contrib"
  File /r ..\..\contrib\*.vo
  SetOutPath "$INSTDIR\lib\theories7"
  File /r ..\..\theories7\*.vo
  SetOutPath "$INSTDIR\lib\contrib7"
  File /r ..\..\contrib7\*.vo
  SetOutPath "$INSTDIR\lib\states"
  File ..\..\states\initial.coq
  SetOutPath "$INSTDIR\lib\states7"
  File ..\..\states7\initial.coq
  File ..\..\states7\barestate.coq
  SetOutPath "$INSTDIR\latex"
  File ..\..\tools\coqdoc\coqdoc.sty
  File ..\..\tools\coqdoc\style.css
  SetOutPath "$INSTDIR\emacs"
  File ..\..\tools\*.el
  SetOutPath "$INSTDIR\man"
  File ..\..\man\*.1

  ;Store install folder
  WriteRegStr HKCU "Software\${MY_PRODUCT}" "" $INSTDIR
  
  ;Create uninstaller
  WriteUninstaller "$INSTDIR\Uninstall.exe"
  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
	  "DisplayName" "Coq Version ${MY_VERSION}"
  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
	  "UninstallString" '"$INSTDIR\Uninstall.exe"'

  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
          "DisplayVersion" "${MY_VERSION}"

  WriteRegDWORD HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
          "NoModify" "1"
  WriteRegDWORD HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
          "NoRepair" "1"

  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
          "URLInfoAbout" "http://coq.inria.fr"

; Start Menu Entries

; for the path in the .lnk
  SetOutPath "$INSTDIR" 

  CreateDirectory "$SMPROGRAMS\Coq"
  CreateShortCut "$SMPROGRAMS\Coq\Coq.lnk" "$INSTDIR\Coq.bat" "" "$INSTDIR\bin\coq.ico" 0
  WriteINIStr "$SMPROGRAMS\Coq\The Coq HomePage.url" "InternetShortcut" "URL" "http://coq.inria.fr"
  WriteINIStr "$SMPROGRAMS\Coq\The Coq Standard Library.url" "InternetShortcut" "URL" "http://coq.inria.fr/library-eng.html"
  CreateShortCut "$SMPROGRAMS\Coq\Uninstall.lnk" "$INSTDIR\Uninstall.exe" "" "$INSTDIR\Uninstall.exe" 0

SectionEnd

Section "CoqIde" Sec2


  SetOutPath "$INSTDIR"
 
  FileOpen $0 $INSTDIR\Coqide.bat w
  FileWrite $0 "@echo off$\r$\n"
  FileWrite $0 "set COQLIB=$INSTDIR\lib$\r$\n"
  FileWrite $0 "set COQBIN=$INSTDIR\bin$\r$\n"
  FileWrite $0 "set HOME=%HOMEPATH%$\r$\n"
  FileWrite $0 "bin\coqide.opt.exe" 
  FileClose $0

  File /oname=.coqiderc ..\..\ide\.coqide-gtk2rc

  SetOutPath "$INSTDIR\bin"
  File ${EXE_PATH}\coqide.*

  ; Start Menu Entries
  CreateShortCut "$SMPROGRAMS\Coq\CoqIde.lnk" "$INSTDIR\Coqide.bat" "" "$INSTDIR\bin\coq.ico" 0 

SectionEnd

Section  "The GTK DLLs (needed by CoqIde)" Sec3
  
  SetOutPath "$INSTDIR\bin"
  File /r /x CVS  dlls\*.*

SectionEnd

;--------------------------------
;Descriptions

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec1} $(DESC_1)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec2} $(DESC_2)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec3} $(DESC_3)
!insertmacro MUI_FUNCTION_DESCRIPTION_END
 
;--------------------------------
;Uninstaller Section

Section "Uninstall"

;; Bat

  Delete "$INSTDIR\Coq.bat"
  Delete "$INSTDIR\Coqide.bat"

;; We keep the settings 
;;  Delete "$INSTDIR\.coqiderc"
 
;; Binaries
  Delete "$INSTDIR\bin\*.exe"
  Delete "$INSTDIR\bin\*.lnk"
 
;; Icon
  Delete "$INSTDIR\bin\coq.ico"

;; DLLs

  Delete "$INSTDIR\bin\*.dll" 
  RMDir /r "$INSTDIR\bin\etc"
  RMDir /r "$INSTDIR\bin\lib"

  RMDir "$INSTDIR\bin"

;; Misc

  Delete "$INSTDIR\latex\coqdoc.sty"
  Delete "$INSTDIR\latex\style.css"
  RMDir "$INSTDIR\latex"

  Delete "$INSTDIR\man\*.1"
  RMDir "$INSTDIR\man"

  Delete "$INSTDIR\emacs\*.el"
  RMDir "$INSTDIR\emacs"

;; Lib

  RMDir /r "$INSTDIR\lib"
  
;; Start Menu
  Delete "$SMPROGRAMS\Coq\Coq.lnk"
  Delete "$SMPROGRAMS\Coq\CoqIde.lnk"
  Delete "$SMPROGRAMS\Coq\Uninstall.lnk"
  Delete "$SMPROGRAMS\Coq\The Coq HomePage.url"
  Delete "$SMPROGRAMS\Coq\The Coq Standard Library.url"
  Delete "$INSTDIR\Uninstall.exe"
  
  DeleteRegKey /ifempty HKCU "Software\${MY_PRODUCT}"

  DeleteRegKey HKEY_LOCAL_MACHINE "SOFTWARE\Coq"
  DeleteRegKey HKEY_LOCAL_MACHINE "SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\Coq"
  RMDir "$INSTDIR"
  RMDir "$SMPROGRAMS\Coq"

SectionEnd