; From NSIS Wiki http://nsis.sourceforge.net/ReplaceInFile
; Modifications:
; - Replace only once per line
; - Don't keep original as .old
; - Use StrRep instead of StrReplace (seems to be cleaner)

Function Func_ReplaceInFile
  ClearErrors

  Exch $0      ; REPLACEMENT
  Exch
  Exch $1      ; SEARCH_TEXT
  Exch 2
  Exch $2      ; SOURCE_FILE

  Push $R0     ; SOURCE_FILE file handle
  Push $R1     ; temporary file handle
  Push $R2     ; unique temporary file name
  Push $R3     ; a line to search and replace / save
  Push $R4     ; shift puffer

  IfFileExists $2 +1 error          ; Check if file exists and open it
  FileOpen $R0 $2 "r"

  GetTempFileName $R2               ; Create temporary output file
  FileOpen $R1 $R2 "w"

  loop:                             ; Loop over lines of file
    FileRead $R0 $R3                ; Read line
    IfErrors finished
    Push "$R3"                      ; Replacine string in line once
    Push "$1"
    Push "$0"
    Call Func_StrRep
    Pop $R3
    FileWrite $R1 "$R3"             ; Write result
  Goto loop

  finished:
    FileClose $R1                   ; Close files
    FileClose $R0
    Delete "$2"                     ; Delete original file and rename temporary file to target
    Rename "$R2" "$2"
    ClearErrors
    Goto out

  error:
    SetErrors

  out:
  Pop $R4
  Pop $R3
  Pop $R2
  Pop $R1
  Pop $R0
  Pop $2
  Pop $0
  Pop $1
FunctionEnd

!macro ReplaceInFile SOURCE_FILE SEARCH_TEXT REPLACEMENT
  Push "${SOURCE_FILE}"
  Push "${SEARCH_TEXT}"
  Push "${REPLACEMENT}"
  Call Func_ReplaceInFile
!macroend

