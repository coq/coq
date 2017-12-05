; This script is used to build the Windows install program for Coq.

; NSIS Modern User Interface
; Written by Joost Verburg
; Modified by Julien Narboux, Pierre Letouzey, Enrico Tassi and Michael Soegtrop

; The following command line defines are expected:
; VERSION      Coq version, e.g. 8.5-pl2
; ARCH         The target architecture, either x86_64 or i686
; COQ_SRC_PATH path of Coq installation in Windows or MinGW format (either \\ or /, but with drive letter)
; COQ_ICON     path of Coq icon file in Windows or MinGW format

; Enable compression after debugging.
; SetCompress off
SetCompressor lzma

!define MY_PRODUCT "Coq" ;Define your own software name here
!define OUTFILE "coq-installer-${VERSION}-${ARCH}.exe"

!include "MUI2.nsh"
!include "FileAssociation.nsh"
!include "StrRep.nsh"
!include "ReplaceInFile.nsh"
!include "winmessages.nsh"

Var COQ_SRC_PATH_BS   ; COQ_SRC_PATH with \ instead of /
Var COQ_SRC_PATH_DBS  ; COQ_SRC_PATH with \\ instead of /
Var INSTDIR_DBS       ; INSTDIR with \\ instead of \

;--------------------------------
;Configuration

  Name "Coq"

  ;General
  OutFile "${OUTFILE}"

  ;Folder selection page
  InstallDir "C:\${MY_PRODUCT}"
  
  ;Remember install folder
  InstallDirRegKey HKCU "Software\${MY_PRODUCT}" ""

;--------------------------------
;Modern UI Configuration
  
  !define MUI_ICON "${COQ_ICON}"

  !insertmacro MUI_PAGE_WELCOME
  !insertmacro MUI_PAGE_LICENSE "${COQ_SRC_PATH}/license_readme/coq/License.txt"
  !insertmacro MUI_PAGE_COMPONENTS
  !define MUI_DIRECTORYPAGE_TEXT_TOP "Select where to install Coq.  The path MUST NOT include spaces."
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
  LangString DESC_1 ${LANG_ENGLISH} "This package contains Coq and CoqIDE."
  LangString DESC_2 ${LANG_ENGLISH} "This package contains an OCaml compiler for Coq native compute and plugin development."
  LangString DESC_3 ${LANG_ENGLISH} "This package contains the development files needed in order to build a plugin for Coq."
  LangString DESC_4 ${LANG_ENGLISH} "Set the OCAMLLIB environment variable for the current user."
  LangString DESC_5 ${LANG_ENGLISH} "Set the OCAMLLIB environment variable for all users."

;--------------------------------
; Check for white spaces
Function .onVerifyInstDir
  StrLen $0 "$INSTDIR"
  StrCpy $1 0
  ${While} $1 < $0
    StrCpy $3 $INSTDIR 1 $1
    StrCmp $3 " " SpacesInPath
    IntOp $1 $1 + 1
  ${EndWhile}
  Goto done
  SpacesInPath:
  Abort
  done:
FunctionEnd

;--------------------------------
;Installer Sections


Section "Coq" Sec1

  SetOutPath "$INSTDIR\"
  !include "..\..\..\filelists\coq_base.nsh"

  ${registerExtension} "$INSTDIR\bin\coqide.exe" ".v" "Coq Script File"

  ;Store install folder
  WriteRegStr HKCU "Software\${MY_PRODUCT}" "" $INSTDIR
  
  ;Create uninstaller
  WriteUninstaller "$INSTDIR\Uninstall.exe"
  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
      "DisplayName" "Coq Version ${VERSION}"
  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
      "UninstallString" '"$INSTDIR\Uninstall.exe"'
  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
      "DisplayVersion" "${VERSION}"
  WriteRegDWORD HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
      "NoModify" "1"
  WriteRegDWORD HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
      "NoRepair" "1"
  WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Coq" \
      "URLInfoAbout" "http://coq.inria.fr"

  ; Create start menu entries
  ; SetOutPath is required for the path in the .lnk files
  SetOutPath "$INSTDIR" 
  CreateDirectory "$SMPROGRAMS\Coq"
  ; The first shortcut set here is treated as main application by Windows 7/8.
  ; Use CoqIDE as main application
  CreateShortCut "$SMPROGRAMS\Coq\CoqIde.lnk" "$INSTDIR\bin\coqide.exe"
  CreateShortCut "$SMPROGRAMS\Coq\Coq.lnk" "$INSTDIR\bin\coqtop.exe"
  WriteINIStr "$SMPROGRAMS\Coq\The Coq HomePage.url" "InternetShortcut" "URL" "http://coq.inria.fr"
  WriteINIStr "$SMPROGRAMS\Coq\The Coq Standard Library.url" "InternetShortcut" "URL" "http://coq.inria.fr/library"
  CreateShortCut "$SMPROGRAMS\Coq\Uninstall.lnk" "$INSTDIR\Uninstall.exe" "" "$INSTDIR\Uninstall.exe" 0

SectionEnd

;OCAML Section "Ocaml for native compute and plugin development" Sec2
;OCAML   SetOutPath "$INSTDIR\"
;OCAML   !include "..\..\..\filelists\ocaml.nsh"
;OCAML 
;OCAML   ; Create a few slash / backslash variants of the source and install path
;OCAML   ; Note: NSIS has variables, written as $VAR and defines, written as ${VAR}
;OCAML   !insertmacro StrRep $COQ_SRC_PATH_BS  ${COQ_SRC_PATH} "/" "\"
;OCAML   !insertmacro StrRep $COQ_SRC_PATH_DBS ${COQ_SRC_PATH} "/" "\\"
;OCAML   !insertmacro StrRep $INSTDIR_DBS      $INSTDIR        "\" "\\"
;OCAML 
;OCAML   ; Replace absolute paths in some OCaml config files
;OCAML   ; These are not all, see ReadMe.txt
;OCAML   !insertmacro ReplaceInFile "$INSTDIR\libocaml\ld.conf" "/"  "\"
;OCAML   !insertmacro ReplaceInFile "$INSTDIR\libocaml\ld.conf" "$COQ_SRC_PATH_BS"  "$INSTDIR"
;OCAML   !insertmacro ReplaceInFile "$INSTDIR\etc\findlib.conf" "$COQ_SRC_PATH_DBS" "$INSTDIR_DBS"
;OCAML SectionEnd
 
Section "Coq files for plugin developers" Sec3
  SetOutPath "$INSTDIR\"
  !include "..\..\..\filelists\coq_plugindev.nsh"
SectionEnd

;OCAML Section "OCAMLLIB current user" Sec4
;OCAML    WriteRegStr HKCU "Environment" "OCAMLLIB" "$INSTDIR\libocaml"
;OCAML    ; This is required, so that a newly started shell gets the new environment variable
;OCAML    ; But it really takes a few seconds
;OCAML    DetailPrint "Broadcasting OCAMLLIB environment variable change (current user)"
;OCAML    SendMessage ${HWND_BROADCAST} ${WM_WININICHANGE} 0 "STR:Environment" /TIMEOUT=1000
;OCAML SectionEnd

;OCAML Section "OCAMLLIB all users" Sec5
;OCAML    WriteRegStr HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "OCAMLLIB" "$INSTDIR\libocaml"
;OCAML    ; This is required, so that a newly started shell gets the new environment variable
;OCAML    ; But it really takes a few seconds
;OCAML    DetailPrint "Broadcasting OCAMLLIB environment variable change (all users)"
;OCAML    SendMessage ${HWND_BROADCAST} ${WM_WININICHANGE} 0 "STR:Environment" /TIMEOUT=1000
;OCAML SectionEnd

;--------------------------------
;Descriptions

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec1} $(DESC_1)
  ;OCAML !insertmacro MUI_DESCRIPTION_TEXT ${Sec2} $(DESC_2)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec3} $(DESC_3)
  ;OCAML !insertmacro MUI_DESCRIPTION_TEXT ${Sec4} $(DESC_4)
  ;OCAML !insertmacro MUI_DESCRIPTION_TEXT ${Sec5} $(DESC_5)
!insertmacro MUI_FUNCTION_DESCRIPTION_END
 
;--------------------------------
;Uninstaller Section

Section "Uninstall"
  ; Files and folders
  RMDir /r "$INSTDIR\bin"
  RMDir /r "$INSTDIR\doc"
  RMDir /r "$INSTDIR\etc"
  RMDir /r "$INSTDIR\lib"
  RMDir /r "$INSTDIR\libocaml"
  RMDir /r "$INSTDIR\share"
  RMDir /r "$INSTDIR\ide"
  RMDir /r "$INSTDIR\gtk-2.0"
  RMDir /r "$INSTDIR\latex"
  RMDir /r "$INSTDIR\license_readme"
  RMDir /r "$INSTDIR\man"
  RMDir /r "$INSTDIR\emacs"

  ; Start Menu
  Delete "$SMPROGRAMS\Coq\Coq.lnk"
  Delete "$SMPROGRAMS\Coq\CoqIde.lnk"
  Delete "$SMPROGRAMS\Coq\Uninstall.lnk"
  Delete "$SMPROGRAMS\Coq\The Coq HomePage.url"
  Delete "$SMPROGRAMS\Coq\The Coq Standard Library.url"
  Delete "$INSTDIR\Uninstall.exe"
  
  ; Registry keys
  DeleteRegKey HKCU "Software\${MY_PRODUCT}"
  DeleteRegKey HKLM "SOFTWARE\Coq"
  DeleteRegKey HKLM "SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\Coq"
  DeleteRegKey HKCU "Environment\OCAMLLIB"
  DeleteRegKey HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment\OCAMLLIB"
  ${unregisterExtension} ".v" "Coq Script File"

  ; Root folders
  RMDir "$INSTDIR"
  RMDir "$SMPROGRAMS\Coq"

SectionEnd
