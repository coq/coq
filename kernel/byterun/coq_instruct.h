/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _COQ_INSTRUCT_
#define _COQ_INSTRUCT_

/* Nota: this list of instructions is parsed to produce derived files */
/* coq_jumptbl.h and copcodes.ml. Instructions should be uppercase    */
/* and alone on lines starting by two spaces.                         */

enum instructions {
  ACC0, ACC1, ACC2, ACC3, ACC4, ACC5, ACC6, ACC7, ACC,
  PUSH, 
  PUSHACC0, PUSHACC1, PUSHACC2, PUSHACC3, PUSHACC4,
  PUSHACC5, PUSHACC6, PUSHACC7, PUSHACC, 
  POP,
  ENVACC1, ENVACC2, ENVACC3, ENVACC4, ENVACC,
  PUSHENVACC1, PUSHENVACC2, PUSHENVACC3, PUSHENVACC4, PUSHENVACC,
  PUSH_RETADDR,
  APPLY, APPLY1, APPLY2, APPLY3, APPLY4,
  APPTERM, APPTERM1, APPTERM2, APPTERM3,
  RETURN, RESTART, GRAB, GRABREC, 
  CLOSURE, CLOSUREREC, CLOSURECOFIX,
  OFFSETCLOSUREM2, OFFSETCLOSURE0, OFFSETCLOSURE2, OFFSETCLOSURE,
  PUSHOFFSETCLOSUREM2, PUSHOFFSETCLOSURE0, PUSHOFFSETCLOSURE2, 
  PUSHOFFSETCLOSURE,
  GETGLOBAL, PUSHGETGLOBAL,
  MAKEBLOCK, MAKEBLOCK1, MAKEBLOCK2, MAKEBLOCK3, MAKEBLOCK4,
  SWITCH, PUSHFIELDS, 
  GETFIELD0, GETFIELD1, GETFIELD, 
  SETFIELD0, SETFIELD1, SETFIELD,
  CONST0, CONST1, CONST2, CONST3, CONSTINT,
  PUSHCONST0, PUSHCONST1, PUSHCONST2, PUSHCONST3, PUSHCONSTINT,
  ACCUMULATE, ACCUMULATECOND, 
  MAKESWITCHBLOCK, MAKEACCU, MAKEPROD, 
  
  BRANCH,
  CHECKADDINT31, ADDINT31, CHECKADDCINT31, CHECKADDCARRYCINT31,
  CHECKSUBINT31, SUBINT31, CHECKSUBCINT31, CHECKSUBCARRYCINT31,
  CHECKMULINT31, CHECKMULCINT31, 
  CHECKDIVINT31, CHECKMODINT31, CHECKDIVEUCLINT31, CHECKDIV21INT31, 
  CHECKLXORINT31, CHECKLORINT31, CHECKLANDINT31, 
  CHECKLSLINT31, CHECKLSRINT31, CHECKADDMULDIVINT31,  
  CHECKLSLINT31CONST1, CHECKLSRINT31CONST1,
  
  CHECKEQINT31, CHECKLTINT31, LTINT31, CHECKLEINT31, LEINT31,
  CHECKCOMPAREINT31,  

  CHECKHEAD0INT31, CHECKTAIL0INT31,

  ISINT, AREINT2, 

  ISINT_CAML_CALL1, ISARRAY_CAML_CALL1, 
  ISINT_CAML_CALL2, ISARRAY_INT_CAML_CALL2, 
  ISARRAY_INT_CAML_CALL3,

  STOP

};

#endif /* _COQ_INSTRUCT_ */
