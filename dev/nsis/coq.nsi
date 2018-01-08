; This script is used to build the Windows install program for Coq.

;NSIS Modern User Interface
;Written by Joost Verburg
;Modified by Julien Narboux and Pierre Letouzey and Enrico Tassi

;SetCompress off
SetCompressor lzma
; Comment out after debuging.

; The VERSION should be passed as an argument at compile time using :
;

!define MY_PRODUCT "Coq" ;Define your own software name here
!define COQ_SRC_PATH "..\.."
!define OUTFILE "coq-${VERSION}-installer-windows-${ARCH}.exe"

!include "MUI2.nsh"
!include "FileAssociation.nsh"

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

  !insertmacro MUI_PAGE_WELCOME
  !insertmacro MUI_PAGE_LICENSE "${COQ_SRC_PATH}/LICENSE"
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
  LangString DESC_2 ${LANG_ENGLISH} "This package contains the development files needed in order to build a plugin for Coq."

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
  File ${COQ_SRC_PATH}\LICENSE

  SetOutPath "$INSTDIR\bin"
  File ${COQ_SRC_PATH}\bin\*.exe
  ; make.exe and its dll
  File ${COQ_SRC_PATH}\bin\make.exe
  File ${COQ_SRC_PATH}\bin\libiconv2.dll
  File ${COQ_SRC_PATH}\bin\libintl3.dll

  SetOutPath "$INSTDIR\lib\theories"
  File /r ${COQ_SRC_PATH}\theories\*.vo
  File /r ${COQ_SRC_PATH}\theories\*.v
  File /r ${COQ_SRC_PATH}\theories\*.glob
  ; File /r ${COQ_SRC_PATH}\theories\*.cmi
  ; File /r ${COQ_SRC_PATH}\theories\*.cmxs
  SetOutPath "$INSTDIR\lib\plugins"
  File /r ${COQ_SRC_PATH}\plugins\*.vo
  File /r ${COQ_SRC_PATH}\plugins\*.v
  File /r ${COQ_SRC_PATH}\plugins\*.glob
  File /r ${COQ_SRC_PATH}\plugins\*.cmi
  File /r ${COQ_SRC_PATH}\plugins\*.cmxs
  SetOutPath "$INSTDIR\lib\tools\coqdoc"
  File ${COQ_SRC_PATH}\tools\coqdoc\coqdoc.sty
  File ${COQ_SRC_PATH}\tools\coqdoc\coqdoc.css
  SetOutPath "$INSTDIR\emacs"
  File ${COQ_SRC_PATH}\tools\*.el
  SetOutPath "$INSTDIR\man"
  File ${COQ_SRC_PATH}\man\*.1
  SetOutPath "$INSTDIR\lib\toploop"
  File ${COQ_SRC_PATH}\stm\*top.cmxs
  File ${COQ_SRC_PATH}\ide\*top.cmxs

  ; CoqIDE
  SetOutPath "$INSTDIR\ide\"
  File ${COQ_SRC_PATH}\ide\*.png
  SetOutPath "$INSTDIR\share\gtksourceview-2.0\language-specs\"
  File ${COQ_SRC_PATH}\ide\*.lang
  File ${COQ_SRC_PATH}\ide\*.xml

  ; Start Menu Entries
  SetOutPath "$INSTDIR"
  CreateShortCut "$SMPROGRAMS\Coq\CoqIde.lnk" "$INSTDIR\bin\coqide.exe"

  ${registerExtension} "$INSTDIR\bin\coqide.exe" ".v" "Coq Script File"

  SetOutPath "$INSTDIR"
  File /r ${GTK_RUNTIME}\etc\gtk-2.0
  SetOutPath "$INSTDIR\bin"
  File ${GTK_RUNTIME}\bin\*.dll
  SetOutPath "$INSTDIR\lib"
  File /r ${GTK_RUNTIME}\lib\gtk-2.0 ${GTK_RUNTIME}\lib\glib-2.0
  SetOutPath "$INSTDIR\share"
  File /r ${GTK_RUNTIME}\share\themes
  File /r ${GTK_RUNTIME}\share\gtksourceview-2.0

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

; Start Menu Entries

; for the path in the .lnk
  SetOutPath "$INSTDIR" 

  CreateDirectory "$SMPROGRAMS\Coq"
  CreateShortCut "$SMPROGRAMS\Coq\Coq.lnk" "$INSTDIR\bin\coqtop.exe"
  WriteINIStr "$SMPROGRAMS\Coq\The Coq HomePage.url" "InternetShortcut" "URL" "http://coq.inria.fr"
  WriteINIStr "$SMPROGRAMS\Coq\The Coq Standard Library.url" "InternetShortcut" "URL" "http://coq.inria.fr/library"
  CreateShortCut "$SMPROGRAMS\Coq\Uninstall.lnk" "$INSTDIR\Uninstall.exe" "" "$INSTDIR\Uninstall.exe" 0

SectionEnd

Section "Coq files for plugin developers" Sec2

  SetOutPath "$INSTDIR\lib\"
  File /r ${COQ_SRC_PATH}\*.cmxa
  File /r ${COQ_SRC_PATH}\*.cmi
  File /r ${COQ_SRC_PATH}\*.cma
  File /r ${COQ_SRC_PATH}\*.cmo
  File /r ${COQ_SRC_PATH}\*.a
  File /r ${COQ_SRC_PATH}\*.o

SectionEnd

;--------------------------------
;Descriptions

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec1} $(DESC_1)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec2} $(DESC_2)
!insertmacro MUI_FUNCTION_DESCRIPTION_END
 
;--------------------------------
;Uninstaller Section

Section "Uninstall"

  RMDir /r "$INSTDIR\bin"
  RMDir /r "$INSTDIR\dev"
  RMDir /r "$INSTDIR\etc"
  RMDir /r "$INSTDIR\lib"
  RMDir /r "$INSTDIR\share"
  RMDir /r "$INSTDIR\ide"

  Delete "$INSTDIR\man\*.1"
  RMDir "$INSTDIR\man"

  Delete "$INSTDIR\emacs\*.el"
  RMDir "$INSTDIR\emacs"

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

  ${unregisterExtension} ".v" "Coq Script File"

SectionEnd
