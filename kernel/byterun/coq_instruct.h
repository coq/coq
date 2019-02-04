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
/* If adding an instruction, DON'T FORGET TO UPDATE coq_fix_code.c    */
/* with the arity of the instruction and maybe coq_tcode_of_code.     */

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
  PROJ,
  ENSURESTACKCAPACITY,
  CONST0, CONST1, CONST2, CONST3, CONSTINT,
  PUSHCONST0, PUSHCONST1, PUSHCONST2, PUSHCONST3, PUSHCONSTINT,
  ACCUMULATE,
  MAKESWITCHBLOCK, MAKEACCU, MAKEPROD, 
/* spiwack: */
  BRANCH,
  CHECKADDINT63, ADDINT63, CHECKADDCINT63, CHECKADDCARRYCINT63,
  CHECKSUBINT63, SUBINT63, CHECKSUBCINT63, CHECKSUBCARRYCINT63,
  CHECKMULINT63, CHECKMULCINT63,
  CHECKDIVINT63, CHECKMODINT63, CHECKDIVEUCLINT63, CHECKDIV21INT63,
  CHECKLXORINT63, CHECKLORINT63, CHECKLANDINT63,
  CHECKLSLINT63, CHECKLSRINT63, CHECKADDMULDIVINT63,
  CHECKLSLINT63CONST1, CHECKLSRINT63CONST1,

  CHECKEQINT63, CHECKLTINT63, LTINT63, CHECKLEINT63, LEINT63,
  CHECKCOMPAREINT63,

  CHECKHEAD0INT63, CHECKTAIL0INT63,

  ISINT, AREINT2,

  STOP
};

#endif /* _COQ_INSTRUCT_ */
