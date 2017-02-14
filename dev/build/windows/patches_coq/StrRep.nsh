; From NSIS Wiki http://nsis.sourceforge.net/StrRep
; Slightly modified

Function Func_StrRep
    Exch $R2 ;new
    Exch 1
    Exch $R1 ;old
    Exch 2
    Exch $R0 ;string
    Push $R3
    Push $R4
    Push $R5
    Push $R6
    Push $R7
    Push $R8
    Push $R9

    StrCpy $R3 0
    StrLen $R4 $R1
    StrLen $R6 $R0
    StrLen $R9 $R2
    loop:
        StrCpy $R5 $R0 $R4 $R3
        StrCmp $R5 $R1 found
        StrCmp $R3 $R6 done
        IntOp $R3 $R3 + 1 ;move offset by 1 to check the next character
        Goto loop
    found:
        StrCpy $R5 $R0 $R3
        IntOp $R8 $R3 + $R4
        StrCpy $R7 $R0 "" $R8
        StrCpy $R0 $R5$R2$R7
        StrLen $R6 $R0
        IntOp $R3 $R3 + $R9 ;move offset by length of the replacement string
        Goto loop
    done:

    Pop $R9
    Pop $R8
    Pop $R7
    Pop $R6
    Pop $R5
    Pop $R4
    Pop $R3
    Push $R0
    Push $R1
    Pop $R0
    Pop $R1
    Pop $R0
    Pop $R2
    Exch $R1
FunctionEnd

!macro StrRep output string old new
    Push `${string}`
    Push `${old}`
    Push `${new}`
    Call Func_StrRep
    Pop ${output}
!macroend
