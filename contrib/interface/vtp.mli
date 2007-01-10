open Ascent;;
open Pp;;

val fCOMMAND_LIST : ct_COMMAND_LIST -> std_ppcmds;;
val fCOMMAND : ct_COMMAND -> std_ppcmds;;
val fTACTIC_COM : ct_TACTIC_COM -> std_ppcmds;;
val fFORMULA : ct_FORMULA -> std_ppcmds;;
val fID : ct_ID -> std_ppcmds;;
val fSTRING : ct_STRING -> std_ppcmds;;
val fINT : ct_INT -> std_ppcmds;;
val fRULE_LIST : ct_RULE_LIST -> std_ppcmds;;
val fRULE : ct_RULE -> std_ppcmds;;
val fSIGNED_INT_LIST : ct_SIGNED_INT_LIST -> std_ppcmds;;
val fPREMISES_LIST : ct_PREMISES_LIST -> std_ppcmds;;
val fID_LIST : ct_ID_LIST -> std_ppcmds;;
val fTEXT : ct_TEXT -> std_ppcmds;;
