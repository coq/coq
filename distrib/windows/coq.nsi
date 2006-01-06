; This script is used to build the Windows install program for Coq.

;NSIS Modern User Interface
;Written by Joost Verburg
;Modified by Julien Narboux

; The VERSION should be passed as an argument at compile time
;
!ifndef VERSION
  !error "VERSION not set"
!endif

!include "MUI.nsh"

; to set COQLIB and COQBIN for all users
!include "WriteEnvStr.nsh"
; to modify PATH
;!include "AddToPath.nsh"

!ifndef OUTFILE
  !define OUTFILE "installer.exe"
!endif

;--------------------------------
;Configuration

  Name "Coq"

  ;General
  OutFile ${OUTFILE}

  ;Folder selection page
  InstallDir "$PROGRAMFILES\Coq"
  
  ;Remember install folder
  InstallDirRegKey HKCU "Software\Coq" ""

  !define Uninstall_Coq_Key \
     'HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq"'

;Interface Configuration

;  !define MUI_HEADERIMAGE
;  !define MUI_HEADERIMAGE_BITMAP "coq_logo.bmp" ; optional
;  !define MUI_ABORTWARNING

  !define MUI_ICON "${NSISDIR}\Contrib\Graphics\Icons\win-install.ico"
  !define MUI_UNICON "${NSISDIR}\Contrib\Graphics\Icons\win-uninstall.ico"

  Icon "coq.ico"

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
  LangString STR_COQ ${LANG_ENGLISH} "This is the windows version of Coq."
  LangString STR_COQIDE ${LANG_ENGLISH} \
    "This is CoqIde, an interactive development environment for Coq."
  LangString STR_GTKDLLS ${LANG_ENGLISH} \
    "This will copy the GTK dlls in the installation directory (These files are needed by CoqIde)."
  LangString STR_USERS ${LANG_ENGLISH} \
    "Check this box to install Coq for all users"

;--------------------------------
;Data
  
;Function .onInit
;  SetOutPath $TEMP
;  File /oname=coq_splash.bmp "coq_splash.bmp"
;	InitPluginsDir
;
;  advsplash::show 1000 600 400 -1 $TEMP\coq_splash
;
;  Pop $0 ; $0 has '1' if the user closed the splash screen early,
;         ; '0' if everything closed normal, and '-1' if some error occured.
;
;  Delete $TEMP\coq_splash.bmp
;FunctionEnd

; Notify the user if Coq was installed for the current user only
Function NotifyInstallUser
  StrCmp $INSTUSER "all users" AllUsersInstOK 
  MessageBox MB_OK|MB_ICONINFORMATION \
    "Warning: Coq could be installed only for the current user"

 AllUsersInstOK:
FunctionEnd


;--------------------------------
;Installer Sections

SetCompress off
;SetCompressor bzip2
; Comment out after debuging.

Section "Coq" Sec1

  SetOutPath "$INSTDIR\bin\"
  FileOpen $0 coqtop.bat w
  FileWrite $0 "@echo off$\r$\n"
  FileWrite $0 "set HOME=$INSTDIR$\r$\n"
  FileWrite $0 '"%COQBIN%\coqtop.opt.exe"' 
  FileClose $0
  CreateShortCut "$INSTDIR\Coq.lnk" \
    "$INSTDIR\bin\coqtop.bat" "" "$INSTDIR\lib\ide\coq.ico" 0

  StrCpy $INSTUSER "all users"

  SetOutPath "$INSTDIR\"
  File /r /x .done "${SOURCEDIR}\*"

  SetOutPath "$INSTDIR\lib\ide"
  File "coq.ico"

  ;Store install folder
  WriteRegStr HKCU "Software\Coq" "" $INSTDIR
  
  ;Create uninstaller
  WriteUninstaller "$INSTDIR\Uninstall.exe"
  WriteRegStr ${Uninstall_Coq_Key} "DisplayName" "Coq Version ${VERSION}"
  WriteRegStr ${Uninstall_Coq_Key} "UninstallString" '"$INSTDIR\Uninstall.exe"'
  WriteRegStr ${Uninstall_Coq_Key} "DisplayVersion" "${VERSION}"
  WriteRegDWORD ${Uninstall_Coq_Key} "NoModify" "1"
  WriteRegDWORD ${Uninstall_Coq_Key} "NoRepair" "1"
  WriteRegStr ${Uninstall_Coq_Key} "URLInfoAbout" "http://coq.inria.fr"

; Environment variables
  Push "COQLIB"
  Push "$INSTDIR\lib"
  Call WriteEnvStr
  Push "COQBIN"
  Push "$INSTDIR\bin"
  Call WriteEnvStr
;  Push "$INSTDIR\bin"
;  Call AddToPath

; Start Menu Entries

; for the path in the .lnk
  SetOutPath "$INSTDIR" 

  CreateDirectory "$SMPROGRAMS\Coq"
  CreateShortCut "$SMPROGRAMS\Coq\Uninstall.lnk" \
    "$INSTDIR\Uninstall.exe" "" "$INSTDIR\Uninstall.exe" 0
  CreateShortCut "$SMPROGRAMS\Coq\Coq.lnk" \
    "$INSTDIR\bin\coqtop.bat" "" "$INSTDIR\lib\ide\coq.ico" 0
  WriteINIStr "$SMPROGRAMS\Coq\The Coq HomePage.url" \
    "InternetShortcut" "URL" "http://coq.inria.fr"
  WriteINIStr "$SMPROGRAMS\Coq\The Coq Standard Library.url" \
    "InternetShortcut" "URL" "http://coq.inria.fr/library-eng.html"

  Call NotifyInstallUser

SectionEnd

Section "CoqIde" Sec2

  SetOutPath "$INSTDIR\bin\"
  FileOpen $0 coqide.bat w
  FileWrite $0 "@echo off$\r$\n"
  FileWrite $0 "set HOME=$INSTDIR$\r$\n"
  FileWrite $0 '"%COQBIN%\coqide.opt.exe"' 
  FileClose $0
  CreateShortCut "$INSTDIR\CoqIde.lnk" \
    "$INSTDIR\bin\coqide.bat" "" "$INSTDIR\lib\ide\coq.ico" 0 SW_SHOWMINIMIZED

  SetOutPath "$INSTDIR"
  File /oname=.coqiderc ..\..\ide\.coqide-gtk2rc
  File /r /x .done "${SOURCEIDEDIR}\*"

  ; Start Menu Entries
  CreateShortCut "$SMPROGRAMS\Coq\CoqIde.lnk" \
    "$INSTDIR\bin\coqide.bat" "" "$INSTDIR\lib\ide\coq.ico" 0 SW_SHOWMINIMIZED

SectionEnd

Section  "The GTK DLLs (needed by CoqIde)" Sec3
  
  SetOutPath "$INSTDIR"
  File /r /x .done dlls\*

SectionEnd
 
;--------------------------------
;Descriptions

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec1} $(STR_COQ)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec2} $(STR_COQIDE)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec3} $(STR_GTKDLLS)
!insertmacro MUI_FUNCTION_DESCRIPTION_END

;--------------------------------
;Uninstaller Section

Section "Uninstall"

;; Bat

  Delete "$INSTDIR\Coq.lnk"
  Delete "$INSTDIR\Coqide.lnk"

;; We keep the settings 
;;  Delete "$INSTDIR\.coqiderc"
 
;; Binaries
  Delete "$INSTDIR\bin\*.exe"
  Delete "$INSTDIR\bin\*.bat"
 
;; Icon
  Delete "$INSTDIR\lib\ide\coq.ico"

;; DLLs

  Delete "$INSTDIR\bin\*.dll" 
  RMDir "$INSTDIR\bin"

;; Misc

  RMDir /r "$INSTDIR\etc\pango"
  RMDir /r "$INSTDIR\etc\gtk-2.0"
  RMDir "$INSTDIR\etc"

  Delete "$INSTDIR\latex\coqdoc.sty"
  Delete "$INSTDIR\latex\style.css"
  RMDir "$INSTDIR\latex"

;  Delete "$INSTDIR\man\man1\*.1"
  RMDir /r "$INSTDIR\man"

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
  
  DeleteRegKey /ifempty HKCU "Software\Coq"

  DeleteRegKey HKLM "SOFTWARE\Coq"
  DeleteRegKey ${Uninstall_Coq_Key}
  RMDir "$INSTDIR"
  RMDir "$SMPROGRAMS\Coq"

;; Environment variable and PATH
  Push "COQLIB"
  Call un.DeleteEnvStr
  Push "COQBIN"
  Call un.DeleteEnvStr
;  Push "$INSTDIR"
;  Call un.RemoveFromPath

SectionEnd