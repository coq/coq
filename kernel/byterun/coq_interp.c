/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

/* The bytecode interpreter */

/* Spiwack: expanded the virtual machine with operators used
   for fast computation of bounded (31bits) integers */

#include <stdio.h>
#include <signal.h>
#include <stdint.h>
#include <caml/memory.h>
#include "coq_gc.h"
#include "coq_instruct.h"
#include "coq_fix_code.h"
#include "coq_memory.h" 
#include "coq_values.h" 

/* spiwack: I append here a few macros for value/number manipulation */
#define uint32_of_value(val) (((uint32_t)(val)) >> 1)
#define value_of_uint32(i)   ((value)((((uint32_t)(i)) << 1) | 1))
#define UI64_of_uint32(lo) ((uint64_t)((uint32_t)(lo)))
#define UI64_of_value(val) (UI64_of_uint32(uint32_of_value(val)))
/* /spiwack */



/* Registers for the abstract machine:
        pc         the code pointer
        sp         the stack pointer (grows downward)
        accu       the accumulator
        env        heap-allocated environment
        trapsp     pointer to the current trap frame
        extra_args number of extra arguments provided by the caller

sp is a local copy of the global variable extern_sp. */



/* Instruction decoding */


#ifdef THREADED_CODE
#  define Instruct(name) coq_lbl_##name: 
#  if defined(ARCH_SIXTYFOUR) && !defined(ARCH_CODE32)
#    define coq_Jumptbl_base ((char *) &&coq_lbl_ACC0)
#  else
#    define coq_Jumptbl_base ((char *) 0)
#    define coq_jumptbl_base ((char *) 0)
#  endif
#  ifdef DEBUG
#    define Next goto next_instr
#  else
#    define Next goto *(void *)(coq_jumptbl_base + *pc++)  
#  endif
#else 
#  define Instruct(name) case name:
#  define Next break
#endif 

/* #define _COQ_DEBUG_ */

#ifdef _COQ_DEBUG_ 
#   define print_instr(s) /*if (drawinstr)*/ printf("%s\n",s)
#   define print_int(i)   /*if (drawinstr)*/ printf("%d\n",i)
#   define print_lint(i)  /*if (drawinstr)*/ printf("%ld\n",i)
# else 
#   define print_instr(s) 
#   define print_int(i) 
#   define print_lint(i)
#endif

#define CHECK_STACK(num_args) {                                                \
if (sp - num_args < coq_stack_threshold) {                                     \
  coq_sp = sp;                                                                 \
  realloc_coq_stack(num_args + Coq_stack_threshold / sizeof(value));           \
  sp = coq_sp;                                                                 \
 }                                                                             \
}

/* GC interface */
#define Setup_for_gc { sp -= 2; sp[0] = accu; sp[1] = coq_env; coq_sp = sp; }
#define Restore_after_gc { accu = sp[0]; coq_env = sp[1]; sp += 2; }


/* Register optimization.
   Some compilers underestimate the use of the local variables representing
   the abstract machine registers, and don't put them in hardware registers,
   which slows down the interpreter considerably.
   For GCC, Xavier Leroy have hand-assigned hardware registers for 
   several architectures.
*/

#if defined(__GNUC__) && !defined(DEBUG)
#ifdef __mips__
#define PC_REG asm("$16")
#define SP_REG asm("$17")
#define ACCU_REG asm("$18")
#endif
#ifdef __sparc__
#define PC_REG asm("%l0")
#define SP_REG asm("%l1")
#define ACCU_REG asm("%l2")
#endif
#ifdef __alpha__
#ifdef __CRAY__
#define PC_REG asm("r9")
#define SP_REG asm("r10")
#define ACCU_REG asm("r11")
#define JUMPTBL_BASE_REG asm("r12")
#else
#define PC_REG asm("$9")
#define SP_REG asm("$10")
#define ACCU_REG asm("$11")
#define JUMPTBL_BASE_REG asm("$12")
#endif
#endif
#ifdef __i386__
#define PC_REG asm("%esi")
#define SP_REG asm("%edi")
#define ACCU_REG
#endif
#if defined(PPC) || defined(_POWER) || defined(_IBMR2)
#define PC_REG asm("26")
#define SP_REG asm("27")
#define ACCU_REG asm("28")
#endif
#ifdef __hppa__
#define PC_REG asm("%r18")
#define SP_REG asm("%r17")
#define ACCU_REG asm("%r16")
#endif
#ifdef __mc68000__
#define PC_REG asm("a5")
#define SP_REG asm("a4")
#define ACCU_REG asm("d7")
#endif
#if defined(__arm__) && !defined(__thumb2__)
#define PC_REG asm("r9")
#define SP_REG asm("r8")
#define ACCU_REG asm("r7")
#endif
#ifdef __ia64__
#define PC_REG asm("36")
#define SP_REG asm("37")
#define ACCU_REG asm("38")
#define JUMPTBL_BASE_REG asm("39")
#endif
#endif

/* For signal handling, we hijack some code from the caml runtime */

extern intnat caml_signals_are_pending;
extern intnat caml_pending_signals[];
extern void caml_process_pending_signals(void);

/* The interpreter itself */

value coq_interprete
(code_t coq_pc, value coq_accu, value coq_atom_tbl, value coq_global_data, value coq_env, long coq_extra_args)
{
  /* coq_accu is not allocated on the OCaml heap */
  CAMLparam2(coq_atom_tbl, coq_global_data);

  /*Declaration des variables */
#ifdef PC_REG
  register code_t pc PC_REG;
  register value * sp SP_REG;
  register value accu ACCU_REG;
#else
  register code_t pc;
  register value * sp;
  register value accu;
#endif
#if defined(THREADED_CODE) && defined(ARCH_SIXTYFOUR) && !defined(ARCH_CODE32)
#ifdef JUMPTBL_BASE_REG
  register char * coq_jumptbl_base JUMPTBL_BASE_REG;
#else
  register char * coq_jumptbl_base;
#endif
#endif
#ifdef THREADED_CODE
  static void * coq_jumptable[] = {
#    include "coq_jumptbl.h"
  };
#else 
  opcode_t curr_instr;
#endif
  print_instr("Enter Interpreter");
  if (coq_pc == NULL) {           /* Interpreter is initializing */
    print_instr("Interpreter is initializing");
#ifdef THREADED_CODE
    coq_instr_table = (char **) coq_jumptable;
    coq_instr_base = coq_Jumptbl_base;
#endif
    CAMLreturn(Val_unit);
  }
#if defined(THREADED_CODE) && defined(ARCH_SIXTYFOUR) && !defined(ARCH_CODE32)
  coq_jumptbl_base = coq_Jumptbl_base;
#endif

  /* Initialisation */
  sp = coq_sp;
  pc = coq_pc;
  accu = coq_accu;

  CHECK_STACK(0);

#ifdef THREADED_CODE
  goto *(void *)(coq_jumptbl_base + *pc++); /* Jump to the first instruction */
#else
  while(1) {
    curr_instr = *pc++;
    switch(curr_instr) {
#endif
/* Basic stack operations */
      
      Instruct(ACC0){
	print_instr("ACC0");
	accu = sp[0]; Next;
      }
      Instruct(ACC1){
	print_instr("ACC1");
	accu = sp[1]; Next;
      }
      Instruct(ACC2){
	print_instr("ACC2");
	accu = sp[2]; Next;
      }
      Instruct(ACC3){
	print_instr("ACC3");
	accu = sp[3]; Next;
      }
      Instruct(ACC4){
	print_instr("ACC4");
	accu = sp[4]; Next;
      }
      Instruct(ACC5){
	print_instr("ACC5");
	accu = sp[5]; Next;
      }
      Instruct(ACC6){
	print_instr("ACC6");
	accu = sp[6]; Next;
      }
      Instruct(ACC7){
	print_instr("ACC7");
        accu = sp[7]; Next;
      }      
      Instruct(PUSH){
	print_instr("PUSH");
	*--sp = accu; Next;
      }
      Instruct(PUSHACC0) {
	print_instr("PUSHACC0");
        *--sp = accu; Next;
      }
      Instruct(PUSHACC1){
	print_instr("PUSHACC1");
        *--sp = accu; accu = sp[1]; Next;
      }
      Instruct(PUSHACC2){
	print_instr("PUSHACC2");
        *--sp = accu; accu = sp[2]; Next;
      }
      Instruct(PUSHACC3){
	print_instr("PUSHACC3");
	*--sp = accu; accu = sp[3]; Next;
      }
      Instruct(PUSHACC4){
	print_instr("PUSHACC4");
	*--sp = accu; accu = sp[4]; Next;
      }
      Instruct(PUSHACC5){
	print_instr("PUSHACC5");
	*--sp = accu; accu = sp[5]; Next;
      }
      Instruct(PUSHACC6){
	print_instr("PUSHACC5");
	*--sp = accu; accu = sp[6]; Next;
      }
      Instruct(PUSHACC7){
	print_instr("PUSHACC7");
	*--sp = accu; accu = sp[7]; Next;
      }
      Instruct(PUSHACC){
	print_instr("PUSHACC");
	*--sp = accu;
      }
      /* Fallthrough */
      
      Instruct(ACC){
	print_instr("ACC");
	accu = sp[*pc++];
        Next;
      }
      
      Instruct(POP){
	print_instr("POP");
	sp += *pc++;
	Next;
      }
      /* Access in heap-allocated environment */
      
      Instruct(ENVACC1){
	print_instr("ENVACC1");
	accu = Field(coq_env, 1); Next;
      }
      Instruct(ENVACC2){
	print_instr("ENVACC2");
	accu = Field(coq_env, 2); Next;
      }
      Instruct(ENVACC3){
	print_instr("ENVACC3");
	accu = Field(coq_env, 3); Next;
      }
      Instruct(ENVACC4){
	print_instr("ENVACC4");
	accu = Field(coq_env, 4); Next;
      }
      Instruct(PUSHENVACC1){
	print_instr("PUSHENVACC1");
	*--sp = accu; accu = Field(coq_env, 1); Next;
      }
      Instruct(PUSHENVACC2){
	print_instr("PUSHENVACC2");
	*--sp = accu; accu = Field(coq_env, 2); Next;
      }
      Instruct(PUSHENVACC3){
	print_instr("PUSHENVACC3");
	*--sp = accu; accu = Field(coq_env, 3); Next;
      }
      Instruct(PUSHENVACC4){
	print_instr("PUSHENVACC4");
	*--sp = accu; accu = Field(coq_env, 4); Next;
      }
      Instruct(PUSHENVACC){
	print_instr("PUSHENVACC");
	*--sp = accu;
      }
      /* Fallthrough */
      Instruct(ENVACC){
	print_instr("ENVACC");
	print_int(*pc);
	accu = Field(coq_env, *pc++);
        Next;
      }
      /* Function application */
      
      Instruct(PUSH_RETADDR) {
	print_instr("PUSH_RETADDR");
	sp -= 3;
	sp[0] = (value) (pc + *pc);
	sp[1] = coq_env;
	sp[2] = Val_long(coq_extra_args);
	coq_extra_args = 0;
	pc++;
	Next;
      }
      Instruct(APPLY) {
	print_instr("APPLY");
	coq_extra_args = *pc - 1;
	pc = Code_val(accu);
	coq_env = accu;
	goto check_stack;
      }
      Instruct(APPLY1) {
	value arg1 = sp[0];
	print_instr("APPLY1");
	sp -= 3;
	sp[0] = arg1;
	sp[1] = (value)pc;
	sp[2] = coq_env;
	sp[3] = Val_long(coq_extra_args);
	print_instr("call stack=");
	print_lint(sp[1]);
	print_lint(sp[2]);
	print_lint(sp[3]);
	pc = Code_val(accu);
	coq_env = accu;
	coq_extra_args = 0;
	goto check_stack;
      }
      Instruct(APPLY2) {
	value arg1 = sp[0];
	value arg2 = sp[1];
	print_instr("APPLY2");
	sp -= 3;
	sp[0] = arg1;
	sp[1] = arg2;
	sp[2] = (value)pc;
	sp[3] = coq_env;
	sp[4] = Val_long(coq_extra_args);
	pc = Code_val(accu);
	coq_env = accu;
	coq_extra_args = 1;
	goto check_stack;
      }
      Instruct(APPLY3) {
	value arg1 = sp[0];
	value arg2 = sp[1];
	value arg3 = sp[2];
	print_instr("APPLY3");
	sp -= 3;
	sp[0] = arg1;
	sp[1] = arg2;
	sp[2] = arg3;
	sp[3] = (value)pc;
	sp[4] = coq_env;
	sp[5] = Val_long(coq_extra_args);
	pc = Code_val(accu);
	coq_env = accu;
	coq_extra_args = 2;
	goto check_stack;
      }
      /* Stack checks */
      
    check_stack:
      print_instr("check_stack");
      CHECK_STACK(0);
      /* We also check for signals */
      if (caml_signals_are_pending) {
	/* If there's a Ctrl-C, we reset the vm */
	if (caml_pending_signals[SIGINT]) { coq_sp = coq_stack_high; }
	caml_process_pending_signals();
      }
      Next;

      Instruct(ENSURESTACKCAPACITY) {
        print_instr("ENSURESTACKCAPACITY");
        int size = *pc++;
        /* CHECK_STACK may trigger here a useless allocation because of the
        threshold, but check_stack: often does it anyway, so we prefer to
        factorize the code. */
        CHECK_STACK(size);
        Next;
      }

      Instruct(APPTERM) {
	int nargs = *pc++;
	int slotsize = *pc;
	value * newsp;
	int i;
	print_instr("APPTERM");
	/* Slide the nargs bottom words of the current frame to the top
	   of the frame, and discard the remainder of the frame */
	newsp = sp + slotsize - nargs;
	for (i = nargs - 1; i >= 0; i--) newsp[i] = sp[i];
	sp = newsp;
	pc = Code_val(accu);
	coq_env = accu;
	coq_extra_args += nargs - 1;
	goto check_stack;
      }
      Instruct(APPTERM1) {
	value arg1 = sp[0];
	print_instr("APPTERM1");
	sp = sp + *pc - 1;
	sp[0] = arg1;
	pc = Code_val(accu);
	coq_env = accu;
	goto check_stack;
      }
      Instruct(APPTERM2) {
	value arg1 = sp[0];
	value arg2 = sp[1];
	print_instr("APPTERM2");
	sp = sp + *pc - 2;
	sp[0] = arg1;
	sp[1] = arg2;
	pc = Code_val(accu);
	print_lint(accu);
	coq_env = accu;
	coq_extra_args += 1;
	goto check_stack;
      }
      Instruct(APPTERM3) {
	value arg1 = sp[0];
	value arg2 = sp[1];
	value arg3 = sp[2];
	print_instr("APPTERM3");
	sp = sp + *pc - 3;
	sp[0] = arg1;
	sp[1] = arg2;
	sp[2] = arg3;
	pc = Code_val(accu);
	coq_env = accu;
	coq_extra_args += 2;
	goto check_stack;
      }
      
      Instruct(RETURN) {
	print_instr("RETURN");
	print_int(*pc);
	sp += *pc++;
	print_instr("stack=");
	print_lint(sp[0]);
	print_lint(sp[1]);
	print_lint(sp[2]);
	if (coq_extra_args > 0) {
	  print_instr("extra args > 0");
	  print_lint(coq_extra_args);
	  coq_extra_args--;
	  pc = Code_val(accu);
	  coq_env = accu;
	} else {
	  print_instr("extra args = 0");
	  pc = (code_t)(sp[0]);
	  coq_env = sp[1];
	  coq_extra_args = Long_val(sp[2]);
	  sp += 3;
	}
	Next;
      }
      
      Instruct(RESTART) {
	int num_args = Wosize_val(coq_env) - 2;
	int i;
	print_instr("RESTART");
        CHECK_STACK(num_args);
	sp -= num_args;
	for (i = 0; i < num_args; i++) sp[i] = Field(coq_env, i + 2);
	coq_env = Field(coq_env, 1);
	coq_extra_args += num_args;
	Next;
      }
      
      Instruct(GRAB) {
	int required = *pc++;
	print_instr("GRAB");
	/*	printf("GRAB %d\n",required); */
	if (coq_extra_args >= required) {
	  coq_extra_args -= required;
	} else {
	  mlsize_t num_args, i;
	  num_args = 1 + coq_extra_args; /* arg1 + extra args */
          Alloc_small(accu, num_args + 2, Closure_tag); 
	  Field(accu, 1) = coq_env;
	  for (i = 0; i < num_args; i++) Field(accu, i + 2) = sp[i];
	  Code_val(accu) = pc - 3; /* Point to the preceding RESTART instr. */
	  sp += num_args;
	  pc = (code_t)(sp[0]);
	  coq_env = sp[1];
	  coq_extra_args = Long_val(sp[2]);
	  sp += 3;
	}
	Next;
      }

      Instruct(GRABREC) { 
	int rec_pos = *pc++; /* commence a zero */
	print_instr("GRABREC");
	if (rec_pos <= coq_extra_args && !Is_accu(sp[rec_pos])) {
	  pc++;/* On saute le Restart */
	} else {
	  if (coq_extra_args < rec_pos) {
            /* Partial application */
	    mlsize_t num_args, i;
	    num_args = 1 + coq_extra_args; /* arg1 + extra args */
	    Alloc_small(accu, num_args + 2, Closure_tag); 
	    Field(accu, 1) = coq_env;
	    for (i = 0; i < num_args; i++) Field(accu, i + 2) = sp[i];
	    Code_val(accu) = pc - 3; 
	    sp += num_args;
	    pc = (code_t)(sp[0]);
	    coq_env = sp[1];
	    coq_extra_args = Long_val(sp[2]);
	    sp += 3;
	  } else {
	    /* The recursif argument is an accumulator */
	    mlsize_t num_args, i;
	    /* Construction of fixpoint applied to its [rec_pos-1] first arguments */
	    Alloc_small(accu, rec_pos + 2, Closure_tag); 
	    Field(accu, 1) = coq_env; // We store the fixpoint in the first field
	    for (i = 0; i < rec_pos; i++) Field(accu, i + 2) = sp[i]; // Storing args
	    Code_val(accu) = pc;
	    sp += rec_pos;
	    *--sp = accu;
	      /* Construction of the atom */
	    Alloc_small(accu, 2, ATOM_FIX_TAG);
	    Field(accu,1) = sp[0];
	    Field(accu,0)  = sp[1];
	    sp++; sp[0] = accu;
	      /* Construction of the accumulator */
	    num_args = coq_extra_args - rec_pos;
	    Alloc_small(accu, 2+num_args, Accu_tag);
	    Code_val(accu) = accumulate;
	    Field(accu,1) = sp[0]; sp++;
	    for (i = 0; i < num_args;i++)Field(accu, i + 2) = sp[i];
	    sp += num_args;
	    pc = (code_t)(sp[0]);
	    coq_env = sp[1];
	    coq_extra_args = Long_val(sp[2]);
	    sp += 3;
	  }
	}
	Next;
      }
	
      Instruct(CLOSURE) {
	int nvars = *pc++;
	int i;
	print_instr("CLOSURE");
	print_int(nvars);
	if (nvars > 0) *--sp = accu;
	Alloc_small(accu, 1 + nvars, Closure_tag);
	Code_val(accu) = pc + *pc;
	pc++;
	for (i = 0; i < nvars; i++) {
	  print_lint(sp[i]);
	  Field(accu, i + 1) = sp[i];
	}
	sp += nvars;
	Next;
      }

      Instruct(CLOSUREREC) {
	int nfuncs = *pc++;
	int nvars = *pc++;
	int start = *pc++;
	int i;
	value * p;
	print_instr("CLOSUREREC");
	if (nvars > 0) *--sp = accu;
	/* construction du vecteur de type */
        Alloc_small(accu, nfuncs, Abstract_tag);
	for(i = 0; i < nfuncs; i++) {
	  Field(accu,i) = (value)(pc+pc[i]);
	}
	pc += nfuncs;
	*--sp=accu;
	Alloc_small(accu, nfuncs * 2 + nvars, Closure_tag);
	Field(accu, nfuncs * 2 + nvars - 1) = *sp++;
	/* On remplie la partie pour les variables libres */
	p = &Field(accu, nfuncs * 2 - 1);
	for (i = 0; i < nvars; i++) {
	  *p++ = *sp++;
	}
	p = &Field(accu, 0);
	*p = (value) (pc + pc[0]);
	p++;
	for (i = 1; i < nfuncs; i++) {
	  *p = Make_header(i * 2, Infix_tag, Caml_white);
	  p++;                                /* color irrelevant. */
	  *p = (value) (pc + pc[i]);
	  p++;
	}
	pc += nfuncs;
	accu = accu + 2 * start * sizeof(value);
	Next;
      }

      Instruct(CLOSURECOFIX){ 
	int nfunc = *pc++;
	int nvars = *pc++;
	int start = *pc++;
	int i, j , size;
	value * p;
	print_instr("CLOSURECOFIX");
	if (nvars > 0) *--sp = accu;
	/* construction du vecteur de type */
        Alloc_small(accu, nfunc, Abstract_tag);
	for(i = 0; i < nfunc; i++) {
	  Field(accu,i) = (value)(pc+pc[i]);
	}
	pc += nfunc;
	*--sp=accu;

        /* Creation des blocks accumulate */
        for(i=0; i < nfunc; i++) {
	  Alloc_small(accu, 2, Accu_tag);
	  Code_val(accu) = accumulate;
	  Field(accu,1) = Val_int(1);
	  *--sp=accu;
	}
	/* creation des fonction cofix */

        p = sp;
	size = nfunc + nvars + 2;
	for (i=0; i < nfunc; i++) {

	  Alloc_small(accu, size, Closure_tag);
	  Code_val(accu) = pc+pc[i];
	  for (j = 0; j < nfunc; j++) Field(accu, j+1) = p[j];
	  Field(accu, size - 1) = p[nfunc];
	  for (j = nfunc+1; j <= nfunc+nvars; j++) Field(accu, j) = p[j];
	  *--sp = accu;
          /* creation du block contenant le cofix */

	  Alloc_small(accu,1, ATOM_COFIX_TAG);
	  Field(accu, 0) = sp[0];
	  *sp = accu;
	  /* mise a jour du block accumulate */
	  caml_modify(&Field(p[i], 1),*sp);
	  sp++;
	}
	pc += nfunc;
	accu = p[start];
        sp = p + nfunc + 1 + nvars;
	print_instr("ici4");
	Next;
      }

    
      Instruct(PUSHOFFSETCLOSURE) {
	print_instr("PUSHOFFSETCLOSURE");
	*--sp = accu;
      } /* fallthrough */
      Instruct(OFFSETCLOSURE) {
	print_instr("OFFSETCLOSURE");
	accu = coq_env + *pc++ * sizeof(value); Next;
      }
      Instruct(PUSHOFFSETCLOSUREM2) {
	print_instr("PUSHOFFSETCLOSUREM2");
	*--sp = accu;
      } /* fallthrough */
      Instruct(OFFSETCLOSUREM2) {
	print_instr("OFFSETCLOSUREM2");
	accu = coq_env - 2 * sizeof(value); Next;
      }
      Instruct(PUSHOFFSETCLOSURE0) {
	print_instr("PUSHOFFSETCLOSURE0");
	*--sp = accu; 
      }/* fallthrough */
      Instruct(OFFSETCLOSURE0) {
	print_instr("OFFSETCLOSURE0");
	accu = coq_env; Next;
      }
      Instruct(PUSHOFFSETCLOSURE2){
	print_instr("PUSHOFFSETCLOSURE2");
	*--sp = accu; /* fallthrough */
      }
      Instruct(OFFSETCLOSURE2) {
	print_instr("OFFSETCLOSURE2");
	accu = coq_env + 2 * sizeof(value); Next;
      }

/* Access to global variables */

      Instruct(PUSHGETGLOBAL) {
	print_instr("PUSH");
	*--sp = accu;
      }
      /* Fallthrough */
      Instruct(GETGLOBAL){
	print_instr("GETGLOBAL");
	print_int(*pc);
	accu = Field(coq_global_data, *pc);
        pc++;
        Next;
      }    

/* Allocation of blocks */

      Instruct(MAKEBLOCK) {
	mlsize_t wosize = *pc++;
	tag_t tag = *pc++;
	mlsize_t i;
	value block;
	print_instr("MAKEBLOCK, tag=");
	Alloc_small(block, wosize, tag);
	Field(block, 0) = accu;
	for (i = 1; i < wosize; i++) Field(block, i) = *sp++;
	accu = block;
	Next;
      }
      Instruct(MAKEBLOCK1) {
	
	tag_t tag = *pc++;
	value block;
	print_instr("MAKEBLOCK1, tag=");
	print_int(tag);
	Alloc_small(block, 1, tag);
	Field(block, 0) = accu;
	accu = block;
	Next;
      }
      Instruct(MAKEBLOCK2) {
	
	tag_t tag = *pc++;
	value block;
	print_instr("MAKEBLOCK2, tag=");
	print_int(tag);
	Alloc_small(block, 2, tag);
	Field(block, 0) = accu;
	Field(block, 1) = sp[0];
	sp += 1;
	accu = block;
	Next;
      }
      Instruct(MAKEBLOCK3) {
	tag_t tag = *pc++;
	value block;
	print_instr("MAKEBLOCK3, tag=");
	print_int(tag);
	Alloc_small(block, 3, tag);
	Field(block, 0) = accu;
	Field(block, 1) = sp[0];
	Field(block, 2) = sp[1];
	sp += 2;
	accu = block;
	Next;
      }
      Instruct(MAKEBLOCK4) {
	tag_t tag = *pc++;
	value block;
	print_instr("MAKEBLOCK4, tag=");
	print_int(tag);
	Alloc_small(block, 4, tag);
	Field(block, 0) = accu;
	Field(block, 1) = sp[0];
	Field(block, 2) = sp[1];
	Field(block, 3) = sp[2];
	sp += 3;
	accu = block;
	Next;
      }

  
/* Access to components of blocks */
        
      Instruct(SWITCH) {
	uint32_t sizes = *pc++;
	print_instr("SWITCH");
	print_int(sizes & 0xFFFFFF);
	if (Is_block(accu)) {
	  long index = Tag_val(accu);
	  print_instr("block");
	  print_lint(index);
	  pc += pc[(sizes & 0xFFFFFF) + index];
	} else {
	  long index = Long_val(accu);
	  print_instr("constant");
	  print_lint(index);
	  pc += pc[index];
	}
	  Next;
      }

      Instruct(PUSHFIELDS){
	int i;
	int size = *pc++;
	print_instr("PUSHFIELDS");
	sp -= size;
	for(i=0;i<size;i++)sp[i] = Field(accu,i);
	Next;
      }
      
      Instruct(GETFIELD0){
	print_instr("GETFIELD0");
	accu = Field(accu, 0); 
	Next;
      }

      Instruct(GETFIELD1){
	print_instr("GETFIELD1");
	accu = Field(accu, 1);
	Next;
      }

      Instruct(GETFIELD){
	print_instr("GETFIELD");
	accu = Field(accu, *pc); 
	pc++; 
	Next;
      }
      
      Instruct(SETFIELD0){
	print_instr("SETFIELD0");
	caml_modify(&Field(accu, 0),*sp);
	sp++;
	Next;
      }
	
      Instruct(SETFIELD1){
	print_instr("SETFIELD1");
	caml_modify(&Field(accu, 1),*sp);
       	sp++;
	Next; 
      }
       
      Instruct(SETFIELD){
	print_instr("SETFIELD");
	caml_modify(&Field(accu, *pc),*sp);
	sp++; pc++;
	Next;
      }


      Instruct(PROJ){
        do_proj:
	print_instr("PROJ");
	if (Is_accu (accu)) {
          *--sp = accu; // Save matched block on stack
          accu = Field(accu, 1); // Save atom to accu register
          switch (Tag_val(accu)) {
          case ATOM_COFIX_TAG: // We are forcing a cofix
            {
              mlsize_t i, nargs;
              sp -= 2;
              // Push the current instruction as the return address
              sp[0] = (value)(pc - 1);
              sp[1] = coq_env;
              coq_env = Field(accu, 0); // Pointer to suspension
              accu = sp[2]; // Save accumulator to accu register
              sp[2] = Val_long(coq_extra_args); // Push number of args for return
              nargs = Wosize_val(accu) - 2; // Number of args = size of accumulator - 1 (accumulator code) - 1 (atom)
              // Push arguments to stack
              CHECK_STACK(nargs + 1);
              sp -= nargs;
              for (i = 0; i < nargs; ++i) sp[i] = Field(accu, i + 2);
              *--sp = accu; // Last argument is the pointer to the suspension
              coq_extra_args = nargs;
              pc = Code_val(coq_env); // Trigger evaluation
              goto check_stack;
            }
          case ATOM_COFIXEVALUATED_TAG:
            {
              accu = Field(accu, 1);
              ++sp;
              goto do_proj;
            }
          default:
            {
              value block;
              /* Skip over the index of projected field */
              ++pc;
              /* Create atom */
              Alloc_small(accu, 2, ATOM_PROJ_TAG);
              Field(accu, 0) = Field(coq_global_data, *pc++);
              Field(accu, 1) = *sp++;
              /* Create accumulator */
              Alloc_small(block, 2, Accu_tag);
              Code_val(block) = accumulate;
              Field(block, 1) = accu;
              accu = block;
            }
          }
	} else {
          accu = Field(accu, *pc);
          pc += 2;
	}
	Next;
      }

/* Integer constants */

      Instruct(CONST0){
	print_instr("CONST0");
	accu = Val_int(0); Next;}
      Instruct(CONST1){
	print_instr("CONST1");
	accu = Val_int(1); Next;}
      Instruct(CONST2){
	print_instr("CONST2");
	accu = Val_int(2); Next;}
      Instruct(CONST3){
	print_instr("CONST3");
	accu = Val_int(3); Next;}
      
      Instruct(PUSHCONST0){
	print_instr("PUSHCONST0");
	*--sp = accu; accu = Val_int(0); Next;
      }
      Instruct(PUSHCONST1){
	print_instr("PUSHCONST1");
	*--sp = accu; accu = Val_int(1); Next;
      }
      Instruct(PUSHCONST2){
	print_instr("PUSHCONST2");
	*--sp = accu; accu = Val_int(2); Next;
      }
      Instruct(PUSHCONST3){
	print_instr("PUSHCONST3");
	*--sp = accu; accu = Val_int(3); Next;
      }

      Instruct(PUSHCONSTINT){
	print_instr("PUSHCONSTINT");
	*--sp = accu;
      }
      /* Fallthrough */
      Instruct(CONSTINT) {
	print_instr("CONSTINT");
	print_int(*pc);
	accu = Val_int(*pc);
	pc++;
	Next;
      }

      /* Special operations for reduction of open term */
      Instruct(ACCUMULATE) {
	mlsize_t i, size;
	print_instr("ACCUMULATE");
	size = Wosize_val(coq_env);
	Alloc_small(accu, size + coq_extra_args + 1, Accu_tag);
	for(i = 0; i < size; i++) Field(accu, i) = Field(coq_env, i);
	for(i = size; i <= coq_extra_args + size; i++) 
	  Field(accu, i) = *sp++;
	pc = (code_t)(sp[0]);
	coq_env = sp[1];
	coq_extra_args = Long_val(sp[2]);
	sp += 3;
	Next;
      }  
      Instruct(MAKESWITCHBLOCK) {
	print_instr("MAKESWITCHBLOCK");
	*--sp = accu; // Save matched block on stack
	accu = Field(accu,1); // Save atom to accu register
	switch (Tag_val(accu)) {
	case ATOM_COFIX_TAG: // We are forcing a cofix
	  {
	    mlsize_t i, nargs;
	    print_instr("COFIX_TAG");
	    sp-=2;
	    pc++;
            // Push the return address
	    sp[0] = (value) (pc + *pc);
	    sp[1] = coq_env;
	    coq_env = Field(accu,0); // Pointer to suspension
	    accu = sp[2]; // Save accumulator to accu register
	    sp[2] = Val_long(coq_extra_args); // Push number of args for return
	    nargs = Wosize_val(accu) - 2; // Number of args = size of accumulator - 1 (accumulator code) - 1 (atom)
            // Push arguments to stack
            CHECK_STACK(nargs+1);
	    sp -= nargs;
	    for (i = 0; i < nargs; i++) sp[i] = Field(accu, i + 2); 
            *--sp = accu; // Leftmost argument is the pointer to the suspension
	    print_lint(nargs);
	    coq_extra_args = nargs;
	    pc = Code_val(coq_env); // Trigger evaluation
	    goto check_stack;
	  }
	case ATOM_COFIXEVALUATED_TAG: 
	  {
	    print_instr("COFIX_EVAL_TAG");
	    accu = Field(accu,1);
	    pc++;
	    pc = pc + *pc;
	    sp++;
	    Next;
	  }
	default: 
	  {  
	    mlsize_t sz;
	    int i, annot;
	    code_t typlbl,swlbl;
	    print_instr("MAKESWITCHBLOCK");
	    
	    typlbl = (code_t)pc + *pc; 
	    pc++;
	    swlbl = (code_t)pc + *pc; 
	    pc++;
	    annot = *pc++;
	    sz = *pc++;
	    *--sp=Field(coq_global_data, annot);
	    /* We save the stack */
	    if (sz == 0) accu = Atom(0);
	    else {
	      Alloc_small(accu, sz, Default_tag);
	      if (Field(*sp, 2) == Val_true) {
		for (i = 0; i < sz; i++) Field(accu, i) = sp[i+2];
	      }else{
		for (i = 0; i < sz; i++) Field(accu, i) = sp[i+5];
	      }
	    }
	    *--sp = accu;
            /* Create bytecode wrappers */
            Alloc_small(accu, 1, Abstract_tag);
            Code_val(accu) = typlbl;
            *--sp = accu;
            Alloc_small(accu, 1, Abstract_tag);
            Code_val(accu) = swlbl;
            *--sp = accu;
            /* We create the switch zipper */
            Alloc_small(accu, 5, Default_tag);
            Field(accu, 0) = sp[1];
            Field(accu, 1) = sp[0];
            Field(accu, 2) = sp[3];
            Field(accu, 3) = sp[2];
            Field(accu, 4) = coq_env;
            sp += 3;
            sp[0] = accu;
	    /* We create the atom */
	    Alloc_small(accu, 2, ATOM_SWITCH_TAG);
	    Field(accu, 0) = sp[1]; Field(accu, 1) = sp[0];
	    sp++;sp[0] = accu;
	    /* We create the accumulator */
	    Alloc_small(accu, 2, Accu_tag);
	    Code_val(accu) = accumulate; 
	    Field(accu,1) = *sp++;
	  }
	}
	Next;
      }

	
         
      Instruct(MAKEACCU) {
	int i;
	print_instr("MAKEACCU");
	Alloc_small(accu, coq_extra_args + 3, Accu_tag);
	Code_val(accu) = accumulate;
	Field(accu,1) = Field(coq_atom_tbl, *pc);
	for(i = 2; i < coq_extra_args + 3; i++) Field(accu, i) = *sp++;
	pc = (code_t)(sp[0]);
	coq_env = sp[1];
	coq_extra_args = Long_val(sp[2]);
	sp += 3;
	Next;
      }
     
      Instruct(MAKEPROD) {
	print_instr("MAKEPROD");
	*--sp=accu;
	Alloc_small(accu,2,0);
	Field(accu, 0) = sp[0];
	Field(accu, 1) = sp[1];
	sp += 2;
	Next;
      }

      /* spiwack: code for interpreting compiled integers */
      Instruct(BRANCH) {
	/* unconditional branching */
        print_instr("BRANCH");
        pc += *pc;
        /* pc = (code_t)(pc+*pc); */
        Next;
      }

      Instruct(ADDINT31) {
        /* Adds the integer in the accumulator with 
           the one ontop of the stack (which is poped)*/
        print_instr("ADDINT31");
        accu = 
           (value)((uint32_t) accu + (uint32_t) *sp++ - 1); 
        /* nota,unlike CaML we don't want
           to have a different behavior depending on the 
           architecture. Thus we cast the operand to uint32 */
        Next;
      }

      Instruct (ADDCINT31) {
	print_instr("ADDCINT31");
	/* returns the sum with a carry */
	uint32_t s;
	s = (uint32_t)accu + (uint32_t)*sp++ - 1;
        if( (uint32_t)s < (uint32_t)accu ) {
          /* carry */
	  Alloc_small(accu, 1, 2); /* ( _ , arity, tag ) */
	}
	else {
	  /*no carry */
	  Alloc_small(accu, 1, 1);
	}
	Field(accu, 0)=(value)s;
	Next;
      }

      Instruct (ADDCARRYCINT31) {
	print_instr("ADDCARRYCINT31");
	/* returns the sum plus one with a carry */
	uint32_t s;
	s = (uint32_t)accu + (uint32_t)*sp++ + 1;
        if( (uint32_t)s <= (uint32_t)accu ) {
          /* carry */
	  Alloc_small(accu, 1, 2); /* ( _ , arity, tag ) */
	}
	else {
	  /*no carry */
	  Alloc_small(accu, 1, 1);
	}
	Field(accu, 0)=(value)s;
	Next;
      }

      Instruct (SUBINT31) {
	print_instr("SUBINT31");
	/* returns the subtraction */
	accu = 
	  (value)((uint32_t) accu - (uint32_t) *sp++ + 1); 
        Next;
      }

      Instruct (SUBCINT31) {
	print_instr("SUBCINT31");
	/* returns the subtraction with a carry */
	uint32_t b;
	uint32_t s;
	b = (uint32_t)*sp++;
	s = (uint32_t)accu - b + 1;
        if( (uint32_t)accu < b ) {
          /* carry */
	  Alloc_small(accu, 1, 2); /* ( _ , arity, tag ) */
	}
	else {
	  /*no carry */
	  Alloc_small(accu, 1, 1);
	}
	Field(accu, 0)=(value)s;
	Next;
      }

      Instruct (SUBCARRYCINT31) {
	print_instr("SUBCARRYCINT31");
	/* returns the subtraction minus one with a carry */
	uint32_t b;
	uint32_t s;
	b = (uint32_t)*sp++;
	s = (value)((uint32_t)accu - b - 1);
        if( (uint32_t)accu <= b ) {
          /* carry */
	  Alloc_small(accu, 1, 2); /* ( _ , arity, tag ) */
	}
	else {
	  /*no carry */
	  Alloc_small(accu, 1, 1);
	}
	Field(accu, 0)=(value)s;
	Next;
      }

      Instruct (MULINT31) {
	/* returns the multiplication */
	print_instr("MULINT31");
        accu = 
	  value_of_uint32((uint32_of_value(accu)) * (uint32_of_value(*sp++)));
	Next;
      }

      Instruct (MULCINT31) {
        /*returns the multiplication on a double size word
          (special case for 0) */
        print_instr("MULCINT31");
	uint64_t p;
        /*accu = 2v+1, *sp=2w+1 ==> p = 2v*w */
        p = UI64_of_value (accu) * UI64_of_uint32 ((*sp++)^1);
	if (p == 0) {
	  accu = (value)1;
	}
	else {
          /* the output type is supposed to have a constant constructor
	     and a non-constant constructor (in that order), the tag
	     of the non-constant constructor is then 1 */
	  Alloc_small(accu, 2, 1); /* ( _ , arity, tag ) */
	  /*unsigned shift*/
	  Field(accu, 0) = (value)((p >> 31)|1) ;  /*higher part*/
	  Field(accu, 1) = (value)((uint32_t)p|1); /*lower part*/
	}
	Next;
      }

      Instruct (DIV21INT31) {
	print_instr("DIV21INT31");
	/* spiwack: takes three int31 (the two first ones represent an
                    int62) and performs the euclidian division of the
                    int62 by the int31 */
        uint64_t bigint;
        bigint = UI64_of_value(accu);
        bigint = (bigint << 31) | UI64_of_value(*sp++);
        uint64_t divisor;
        divisor = UI64_of_value(*sp++);
        Alloc_small(accu, 2, 1); /* ( _ , arity, tag ) */
        if (divisor == 0) {
          Field(accu, 0) = 1; /* 2*0+1 */
          Field(accu, 1) = 1; /* 2*0+1 */
	}
	else {
	  uint64_t quo, mod;
	  quo = bigint / divisor;
	  mod = bigint % divisor;
          Field(accu, 0) = value_of_uint32((uint32_t)(quo));
	  Field(accu, 1) = value_of_uint32((uint32_t)(mod));
	}
	Next;
      }

      Instruct (DIVINT31) {
	print_instr("DIVINT31");
        /* spiwack: a priori no need of the NON_STANDARD_DIV_MOD flag
                    since it probably only concerns negative number.
                    needs to be checked at this point */
        uint32_t divisor;
        divisor = uint32_of_value(*sp++);
        if (divisor == 0) { 
          Alloc_small(accu, 2, 1); /* ( _ , arity, tag ) */
	  Field(accu, 0) = 1; /* 2*0+1 */
          Field(accu, 1) = 1; /* 2*0+1 */
        }
        else {
          uint32_t modulus;
          modulus = uint32_of_value(accu);
          Alloc_small(accu, 2, 1); /* ( _ , arity, tag ) */
	  Field(accu, 0) = value_of_uint32(modulus/divisor);
          Field(accu, 1) = value_of_uint32(modulus%divisor);
        }
	Next;
      }

      Instruct (ADDMULDIVINT31) {
        print_instr("ADDMULDIVINT31");
        /* higher level shift (does shifts and cycles and such) */
        uint32_t shiftby;
        shiftby = uint32_of_value(accu);
        if (shiftby > 31) {
          if (shiftby < 62) {
            sp++;
	    accu = (value)(((((uint32_t)*sp++)^1) << (shiftby - 31)) | 1);
          }
          else {
            sp+=2;
            accu = (value)(1);
          }
	}
        else{
        /* *sp = 2*x+1 --> accu = 2^(shiftby+1)*x */
	  accu = (value)((((uint32_t)*sp++)^1) << shiftby);
        /* accu = 2^(shiftby+1)*x --> 2^(shifby+1)*x+2*y/2^(31-shiftby)+1 */
        accu = (value)((accu | (((uint32_t)(*sp++)) >> (31-shiftby)))|1);
	}
        Next;
      }

      Instruct (COMPAREINT31) {
	/* returns Eq if equal, Lt if accu is less than *sp, Gt otherwise */
	/* assumes Inductive _ : _ := Eq | Lt | Gt */
	print_instr("COMPAREINT31");
	if ((uint32_t)accu == (uint32_t)*sp) {
	  accu = 1;  /* 2*0+1 */
	  sp++;
	}
	else{if ((uint32_t)accu < (uint32_t)(*sp++)) {
	  accu = 3;  /* 2*1+1 */
	}
	else{
	  accu = 5;   /* 2*2+1 */
	}}
        Next;
      }
 
      Instruct (HEAD0INT31) {
	int r = 0;
        uint32_t x;
        print_instr("HEAD0INT31");
	x = (uint32_t) accu;
        if (!(x & 0xFFFF0000)) { x <<= 16; r += 16; }
        if (!(x & 0xFF000000)) { x <<= 8;  r += 8; }
        if (!(x & 0xF0000000)) { x <<= 4;  r += 4; }
        if (!(x & 0xC0000000)) { x <<= 2;  r += 2; }
        if (!(x & 0x80000000)) { x <<=1;   r += 1; }
        if (!(x & 0x80000000)) {           r += 1; }
        accu = value_of_uint32(r);
        Next;
      }
        
      Instruct (TAIL0INT31) {
	int r = 0;
        uint32_t x;
        print_instr("TAIL0INT31");
	x = (((uint32_t) accu >> 1) | 0x80000000);
        if (!(x & 0xFFFF)) { x >>= 16; r += 16; }
        if (!(x & 0x00FF)) { x >>= 8;  r += 8; }
        if (!(x & 0x000F)) { x >>= 4;  r += 4; }
        if (!(x & 0x0003)) { x >>= 2;  r += 2; }
        if (!(x & 0x0001)) { x >>=1;   r += 1; }
        if (!(x & 0x0001)) {           r += 1; }
        accu = value_of_uint32(r);
        Next;
      }

      Instruct (ISCONST) {
        /* Branches if the accu does not contain a constant
           (i.e., a non-block value) */
        print_instr("ISCONST");
        if ((accu & 1) == 0) /* last bit is 0 -> it is a block */
	  pc +=  *pc;
        else
	  pc++;
        Next;

      }

      Instruct (ARECONST) {
        /* Branches if the n first values on the stack are not
           all constansts */
        print_instr("ARECONST");
        int i, n, ok;
        ok = 1;
        n = *pc++;
        for(i=0; i < n; i++) {
          if ((sp[i] & 1) == 0) {
	    ok = 0;
            break;
          }
        }
        if(ok) pc++; else pc += *pc;
        Next;
      }

      Instruct (COMPINT31) {
        /* makes an 31-bit integer out of the accumulator and
           the 30 first values of the stack 
           and put it in the accumulator (the accumulator then the 
           topmost get to be the heavier bits) */
        print_instr("COMPINT31");
        int i;
        /*accu=accu or accu = (value)((unsigned long)1-accu) if bool
	               is used for the bits */
        for(i=0; i < 30; i++) {
	  accu = (value) ((((uint32_t)accu-1) << 1) | *sp++);
          /* -1 removes the tag bit, << 1 multiplies the value by 2, 
              | *sp++ pops the last value and add it (no carry involved)
	      not that it reintroduces a tag bit */
          /* alternative, if bool is used for the bits :
	     accu = (value) ((((unsigned long)accu) << 1) & !*sp++); */
        }
        Next;
      }

      Instruct (DECOMPINT31) {
        /* builds a block out of a 31-bit integer (from the accumulator), 
           used before cases */
        int i;
	value block;
	print_instr("DECOMPINT31");
        Alloc_small(block, 31, 1); // Alloc_small(*, size, tag)
        for(i = 30; i >= 0; i--) {
          Field(block, i) = (value)(accu & 3); /* two last bits of the accumulator */
          //Field(block, i) = 3;
          accu = (value) ((uint32_t)accu >> 1) | 1;  /* last bit must be a one */
        };
	accu = block;
        Next;
      }

      Instruct (ORINT31) {
	/* returns the bitwise or */
	print_instr("ORINT31");
        accu =
	  value_of_uint32((uint32_of_value(accu)) | (uint32_of_value(*sp++)));
	Next;
      }

      Instruct (ANDINT31) {
	/* returns the bitwise and */
	print_instr("ANDINT31");
        accu =
	  value_of_uint32((uint32_of_value(accu)) & (uint32_of_value(*sp++)));
	Next;
      }

      Instruct (XORINT31) {
	/* returns the bitwise xor */
	print_instr("XORINT31");
        accu =
	  value_of_uint32((uint32_of_value(accu)) ^ (uint32_of_value(*sp++)));
	Next;
      }

      /*  /spiwack   */



/* Debugging and machine control */

      Instruct(STOP){
	print_instr("STOP");
	coq_sp = sp;
        CAMLreturn(accu);
      }
      
  
#ifndef THREADED_CODE
    default:
      /*fprintf(stderr, "%d\n", *pc);*/
      failwith("Coq VM: Fatal error: bad opcode");
    }
  }
#endif
}

value coq_push_ra(value code) {
  code_t tcode = Code_val(code);
  print_instr("push_ra");
  coq_sp -= 3;
  coq_sp[0] = (value) tcode;
  coq_sp[1] = Val_unit;
  coq_sp[2] = Val_long(0);
  return Val_unit;
}

value coq_push_val(value v) {
  print_instr("push_val");
  *--coq_sp = v;
  return Val_unit;
}

value coq_push_arguments(value args) {
  int nargs,i;
  value * sp = coq_sp;
  nargs = Wosize_val(args) - 2;
  CHECK_STACK(nargs);
  coq_sp -= nargs;
  print_instr("push_args");print_int(nargs);
  for(i = 0; i < nargs; i++) coq_sp[i] = Field(args, i+2);
  return Val_unit;
}

value coq_push_vstack(value stk, value max_stack_size) {
  int len,i;
  value * sp = coq_sp;
  len = Wosize_val(stk);
  CHECK_STACK(len);
  coq_sp -= len;
  print_instr("push_vstack");print_int(len);
   for(i = 0; i < len; i++) coq_sp[i] = Field(stk,i);
  sp = coq_sp;
  CHECK_STACK(uint32_of_value(max_stack_size));
  return Val_unit;
}

value  coq_interprete_ml(value tcode, value a, value t, value g, value e, value ea) {
  // Registering the other arguments w.r.t. the OCaml GC is done by coq_interprete
  CAMLparam1(tcode);
  print_instr("coq_interprete");
  CAMLreturn (coq_interprete(Code_val(tcode), a, t, g, e, Long_val(ea)));
  print_instr("end coq_interprete");
}

value coq_interprete_byte(value* argv, int argn){
  return coq_interprete_ml(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value coq_eval_tcode (value tcode, value t, value g, value e) {
  return coq_interprete_ml(tcode, Val_unit, t, g, e, 0);
}
