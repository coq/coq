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
#include <math.h>

#define CAML_INTERNALS
#include <caml/memory.h>
#include <caml/signals.h>
#include <caml/version.h>
#include <caml/callback.h>

#include "coq_instruct.h"
#include "coq_fix_code.h"
#include "coq_memory.h"
#include "coq_values.h"

#if OCAML_VERSION < 41000
extern void caml_minor_collection(void);

#undef Alloc_small
#define Alloc_small(result, wosize, tag) do{                            \
  caml_young_ptr -= Bhsize_wosize(wosize);                              \
  if (caml_young_ptr < caml_young_limit) {                              \
    caml_young_ptr += Bhsize_wosize(wosize);                            \
    Setup_for_gc;                                                       \
    caml_minor_collection();                                            \
    Restore_after_gc;                                                   \
    caml_young_ptr -= Bhsize_wosize(wosize);                            \
  }                                                                     \
  Hd_hp(caml_young_ptr) = Make_header((wosize), (tag), Caml_black);     \
  (result) = Val_hp(caml_young_ptr);                                    \
  }while(0)
#endif

#ifdef ARCH_SIXTYFOUR
#include "coq_uint63_native.h"
#else
#include "coq_uint63_emul.h"
#endif



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
#define Setup_for_caml_call { *--sp = coq_env; coq_sp = sp; }
#define Restore_after_caml_call coq_env = *sp++;

#if OCAML_VERSION >= 50000
#define Coq_alloc_small(result, wosize, tag) Alloc_small(result, wosize, tag, \
  { Setup_for_gc; caml_process_pending_actions(); Restore_after_gc; })
#else
#define Coq_alloc_small(result, wosize, tag) Alloc_small(result, wosize, tag)
#endif

/* Register optimization.
   Some compilers underestimate the use of the local variables representing
   the abstract machine registers, and don't put them in hardware registers,
   which slows down the interpreter considerably.
   For GCC, Xavier Leroy have hand-assigned hardware registers for
   several architectures.
*/

#if defined(__GNUC__) && !defined(DEBUG) && !defined(__INTEL_COMPILER) \
    && !defined(__llvm__)
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
#if defined(__ppc__) || defined(__ppc64__)
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
/* OCaml PR#4953: these specific registers not available in Thumb mode */
#if defined(__arm__) && !defined(__thumb__)
#define PC_REG asm("r6")
#define SP_REG asm("r8")
#define ACCU_REG asm("r7")
#endif
#ifdef __ia64__
#define PC_REG asm("36")
#define SP_REG asm("37")
#define ACCU_REG asm("38")
#define JUMPTBL_BASE_REG asm("39")
#endif
#ifdef __x86_64__
#define PC_REG asm("%r15")
#define SP_REG asm("%r14")
#define ACCU_REG asm("%r13")
#endif
#ifdef __aarch64__
#define PC_REG asm("%x19")
#define SP_REG asm("%x20")
#define ACCU_REG asm("%x21")
#define JUMPTBL_BASE_REG asm("%x22")
#endif
#endif

/* We should also check "Code_val(v) == accumulate" to be sure,
   but Is_accu is only used in places where closures cannot occur. */
#define Is_accu(v) (Is_block(v) && Tag_val(v) == Closure_tag)

#define CheckPrimArgs(cond, apply_lbl) do{         \
    if (cond) pc++;                                \
    else{                                          \
      *--sp=accu;                                  \
      accu = Field(coq_global_data, *pc++);        \
      goto apply_lbl;                              \
    }                                              \
  }while(0)

#define CheckInt1() CheckPrimArgs(Is_uint63(accu), apply1)
#define CheckInt2() CheckPrimArgs(Is_uint63(accu) && Is_uint63(sp[0]), apply2)
#define CheckInt3() CheckPrimArgs(Is_uint63(accu) && Is_uint63(sp[0]) \
                                                  && Is_uint63(sp[1]), apply3)
#define CheckFloat1() CheckPrimArgs(Is_double(accu), apply1)
#define CheckFloat2() CheckPrimArgs(Is_double(accu) && Is_double(sp[0]), apply2)

#define AllocCarry(cond) Coq_alloc_small(accu, 1, (cond)? coq_tag_C1 : coq_tag_C0)
#define AllocPair() Coq_alloc_small(accu, 2, coq_tag_pair)

/* Beware: we cannot use caml_copy_double here as it doesn't use
   Alloc_small, hence doesn't protect the stack via
   Setup_for_gc/Restore_after_gc. */
#define Coq_copy_double(val) do{                   \
  double Coq_copy_double_f__ = (val);              \
  Coq_alloc_small(accu, Double_wosize, Double_tag);\
  Store_double_val(accu, Coq_copy_double_f__);     \
  }while(0);

#define Swap_accu_sp do{                        \
    value swap_accu_sp_tmp__ = accu;            \
    accu = *sp;                                 \
    *sp = swap_accu_sp_tmp__;                   \
  }while(0)

/* Turn a code pointer into a stack value usable as a return address, and conversely.
   The least significant bit is set to 1 so that the GC does not mistake return
   addresses for heap pointers. */
#define StoreRA(p) ((value)(p) + 1)
#define LoadRA(p) ((code_t)((value)(p) - 1))

#if OCAML_VERSION < 41000
/* For signal handling, we hijack some code from the caml runtime */

extern intnat volatile caml_signals_are_pending;
extern intnat volatile caml_pending_signals[];
extern void caml_process_pending_signals(void);
#endif

extern double coq_next_up(double);
extern double coq_next_down(double);

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

      Instruct(ENVACC0){
        print_instr("ENVACC0");
        accu = Field(coq_env, 2);
        Next;
      }
      Instruct(ENVACC1){
        print_instr("ENVACC1");
        accu = Field(coq_env, 3);
        Next;
      }
      Instruct(ENVACC2){
        print_instr("ENVACC2");
        accu = Field(coq_env, 4);
        Next;
      }
      Instruct(ENVACC3){
        print_instr("ENVACC3");
        accu = Field(coq_env, 5);
        Next;
      }
      Instruct(PUSHENVACC0){
        print_instr("PUSHENVACC0");
        *--sp = accu;
        accu = Field(coq_env, 2);
        Next;
      }
      Instruct(PUSHENVACC1){
        print_instr("PUSHENVACC1");
        *--sp = accu;
        accu = Field(coq_env, 3);
        Next;
      }
      Instruct(PUSHENVACC2){
        print_instr("PUSHENVACC2");
        *--sp = accu;
        accu = Field(coq_env, 4);
        Next;
      }
      Instruct(PUSHENVACC3){
        print_instr("PUSHENVACC3");
        *--sp = accu;
        accu = Field(coq_env, 5);
        Next;
      }
      Instruct(PUSHENVACC){
        print_instr("PUSHENVACC");
        *--sp = accu;
      }
      /* Fallthrough */
      Instruct(ENVACC){
        print_instr("ENVACC");
        print_int(*pc);
        accu = Field(coq_env, 2 + *pc++);
        Next;
      }
      /* Function application */

      Instruct(PUSH_RETADDR) {
        print_instr("PUSH_RETADDR");
        sp -= 3;
        sp[0] = StoreRA(pc + *pc);
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
        value arg1;
      apply1:
        print_instr("APPLY1");
        arg1 = sp[0];
        sp -= 3;
        sp[0] = arg1;
        sp[1] = StoreRA(pc);
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
        value arg1;
        value arg2;
      apply2:
        print_instr("APPLY2");
        arg1 = sp[0];
        arg2 = sp[1];
        sp -= 3;
        sp[0] = arg1;
        sp[1] = arg2;
        sp[2] = StoreRA(pc);
        sp[3] = coq_env;
        sp[4] = Val_long(coq_extra_args);
        pc = Code_val(accu);
        coq_env = accu;
        coq_extra_args = 1;
        goto check_stack;
      }

      Instruct(APPLY3) {
        value arg1;
        value arg2;
        value arg3;
      apply3:
        print_instr("APPLY3");
        arg1 = sp[0];
        arg2 = sp[1];
        arg3 = sp[2];
        sp -= 3;
        sp[0] = arg1;
        sp[1] = arg2;
        sp[2] = arg3;
        sp[3] = StoreRA(pc);
        sp[4] = coq_env;
        sp[5] = Val_long(coq_extra_args);
        pc = Code_val(accu);
        coq_env = accu;
        coq_extra_args = 2;
        goto check_stack;
      }

       Instruct(APPLY4) {
        value arg1 = sp[0];
        value arg2 = sp[1];
        value arg3 = sp[2];
        value arg4 = sp[3];
        print_instr("APPLY4");
        sp -= 3;
        sp[0] = arg1;
        sp[1] = arg2;
        sp[2] = arg3;
        sp[3] = arg4;
        sp[4] = StoreRA(pc);
        sp[5] = coq_env;
        sp[6] = Val_long(coq_extra_args);
        pc = Code_val(accu);
        coq_env = accu;
        coq_extra_args = 3;
        goto check_stack;
      }

     /* Stack checks */

    check_stack:
      print_instr("check_stack");
      CHECK_STACK(0);
      /* We also check for signals */
#if OCAML_VERSION >= 50000
      if (Caml_check_gc_interrupt(Caml_state) || caml_check_for_pending_signals()) {
        // FIXME: it should be caml_process_pending_actions_exn
        value res = caml_process_pending_signals_exn();
        if (Is_exception_result(res)) {
          /* If there is an asynchronous exception, we reset the vm */
          coq_sp = coq_stack_high;
          caml_raise(Extract_exception(res));
        }
      }
#elif OCAML_VERSION >= 41000
      if (caml_something_to_do) {
        value res = caml_process_pending_actions_exn();
        if (Is_exception_result(res)) {
          /* If there is an asynchronous exception, we reset the vm */
          coq_sp = coq_stack_high;
          caml_raise(Extract_exception(res));
        }
      }
#else
      if (caml_signals_are_pending) {
        /* If there's a Ctrl-C, we reset the vm */
        intnat sigint = caml_pending_signals[SIGINT];
        if (sigint) { coq_sp = coq_stack_high; }
        caml_process_pending_signals();
        if (sigint) {
          caml_failwith("Coq VM: Fatal error: SIGINT signal detected "
                        "but no exception was raised");
        }
      }
#endif
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
          pc = LoadRA(sp[0]);
          coq_env = sp[1];
          coq_extra_args = Long_val(sp[2]);
          sp += 3;
        }
        Next;
      }

      Instruct(RESTART) {
        int num_args = Wosize_val(coq_env) - 3;
        int i;
        print_instr("RESTART");
        CHECK_STACK(num_args);
        sp -= num_args;
        for (i = 0; i < num_args; i++) sp[i] = Field(coq_env, i + 3);
        coq_env = Field(coq_env, 2);
        coq_extra_args += num_args;
        Next;
      }

      Instruct(GRAB) {
        int required = *pc++;
        print_instr("GRAB");
        /*      printf("GRAB %d\n",required); */
        if (coq_extra_args >= required) {
          coq_extra_args -= required;
        } else {
          mlsize_t num_args, i;
          num_args = 1 + coq_extra_args; /* arg1 + extra args */
          Coq_alloc_small(accu, num_args + 3, Closure_tag);
          Field(accu, 1) = Val_int(2);
          Field(accu, 2) = coq_env;
          for (i = 0; i < num_args; i++) Field(accu, i + 3) = sp[i];
          Code_val(accu) = pc - 3; /* Point to the preceding RESTART instr. */
          sp += num_args;
          pc = LoadRA(sp[0]);
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
          pc++; /* Skip the next RESTART, then point coq_env at the free variables. */
          coq_env = coq_env + (Int_val(Field(coq_env, 1)) - 2) * sizeof(value);
        } else {
          if (coq_extra_args < rec_pos) {
            /* Partial application */
            mlsize_t num_args, i;
            num_args = 1 + coq_extra_args; /* arg1 + extra args */
            Coq_alloc_small(accu, num_args + 3, Closure_tag);
            Code_val(accu) = pc - 3; /* Point to the preceding RESTART instr. */
            Field(accu, 1) = Val_int(2);
            Field(accu, 2) = coq_env;
            for (i = 0; i < num_args; i++) Field(accu, i + 3) = sp[i];
            sp += num_args;
            pc = LoadRA(sp[0]);
            coq_env = sp[1];
            coq_extra_args = Long_val(sp[2]);
            sp += 3;
          } else {
            /* The recursive argument is an accumulator */
            mlsize_t num_args, sz, i;
            value block;
            /* Construction of fixpoint applied to its [rec_pos-1] first arguments */
            Coq_alloc_small(accu, rec_pos + 3, Closure_tag);
            Code_val(accu) = pc; /* Point to the next RESTART instr. */
            Field(accu, 1) = Val_int(2);
            Field(accu, 2) = coq_env; // We store the fixpoint in the first field
            for (i = 0; i < rec_pos; i++) Field(accu, i + 3) = *sp++; // Storing args
            /* Construction of the atom */
            Coq_alloc_small(block, 2, ATOM_FIX_TAG);
            Field(block, 0) = *sp++;
            Field(block, 1) = accu;
            accu = block;
            /* Construction of the accumulator */
            num_args = coq_extra_args - rec_pos;
            sz = 3 + num_args;
            if (sz <= Max_young_wosize) {
              Coq_alloc_small(block, sz, Closure_tag);
              Field(block, 2) = accu;
              for (i = 3; i < sz; ++i)
                Field(block, i) = *sp++;
            } else {
              // too large for Alloc_small, so use caml_alloc_shr instead
              // it never triggers a GC, so no need for Setup_for_gc
              block = caml_alloc_shr(sz, Closure_tag);
              caml_initialize(&Field(block, 2), accu);
              for (i = 3; i < sz; ++i)
                caml_initialize(&Field(block, i), *sp++);
            }
            Code_val(block) = accumulate;
            Field(block, 1) = Val_int(2);
            accu = block;
            pc = LoadRA(sp[0]);
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
        Coq_alloc_small(accu, 2 + nvars, Closure_tag);
        Field(accu, 1) = Val_int(2);
        Code_val(accu) = pc + *pc;
        pc++;
        for (i = 0; i < nvars; i++) {
          print_lint(sp[i]);
          Field(accu, i + 2) = sp[i];
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
        Coq_alloc_small(accu, nfuncs, Abstract_tag);
        for(i = 0; i < nfuncs; i++) {
          Field(accu,i) = (value)(pc+pc[i]);
        }
        pc += nfuncs;
        *--sp=accu;
        Coq_alloc_small(accu, nfuncs * 3 + nvars, Closure_tag);
        Field(accu, nfuncs * 3 + nvars - 1) = *sp++;
        p = &Field(accu, 0);
        *p++ = (value) (pc + pc[0]);
        *p++ = Val_int(nfuncs * 3 - 1);
        for (i = 1; i < nfuncs; i++) {
          *p++ = Make_header(i * 3, Infix_tag, 0); /* color irrelevant. */
          *p++ = (value) (pc + pc[i]);
          *p++ = Val_int((nfuncs - i) * 3 - 1);
        }
        for (i = 0; i < nvars; i++) *p++ = *sp++;
        pc += nfuncs;
        accu = accu + start * 3 * sizeof(value);
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
        Coq_alloc_small(accu, nfunc, Abstract_tag);
        for(i = 0; i < nfunc; i++) {
          Field(accu,i) = (value)(pc+pc[i]);
        }
        pc += nfunc;
        *--sp=accu;

        /* Creation des blocks accumulate */
        for(i=0; i < nfunc; i++) {
          Coq_alloc_small(accu, 3, Closure_tag);
          Code_val(accu) = accumulate;
          Field(accu, 1) = Val_int(2);
          Field(accu, 2) = Val_int(1);
          *--sp=accu;
        }
        /* creation des fonction cofix */

        p = sp;
        size = nfunc + nvars + 3;
        for (i=0; i < nfunc; i++) {
          value block;
          Coq_alloc_small(accu, size, Closure_tag);
          Code_val(accu) = pc+pc[i];
          Field(accu, 1) = Val_int(2);
          for (j = 0; j < nfunc; ++j) Field(accu, j + 2) = p[j];
          Field(accu, size - 1) = p[nfunc];
          for (j = nfunc + 1; j <= nfunc + nvars; ++j) Field(accu, j + 1) = p[j];
          Coq_alloc_small(block, 1, ATOM_COFIX_TAG);
          Field(block, 0) = accu;
          /* update the accumulate block */
          caml_modify(&Field(p[i], 2), block);
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
        accu = coq_env - *pc++ * 3 * sizeof(value);
        Next;
      }
      Instruct(PUSHOFFSETCLOSURE0) {
        print_instr("PUSHOFFSETCLOSURE0");
        *--sp = accu;
      }/* fallthrough */
      Instruct(OFFSETCLOSURE0) {
        print_instr("OFFSETCLOSURE0");
        accu = coq_env;
        Next;
      }
      Instruct(PUSHOFFSETCLOSURE1){
        print_instr("PUSHOFFSETCLOSURE1");
        *--sp = accu; /* fallthrough */
      }
      Instruct(OFFSETCLOSURE1) {
        print_instr("OFFSETCLOSURE1");
        accu = coq_env - 3 * sizeof(value);
        Next;
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
        Coq_alloc_small(block, wosize, tag);
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
        Coq_alloc_small(block, 1, tag);
        Field(block, 0) = accu;
        accu = block;
        Next;
      }
      Instruct(MAKEBLOCK2) {

        tag_t tag = *pc++;
        value block;
        print_instr("MAKEBLOCK2, tag=");
        print_int(tag);
        Coq_alloc_small(block, 2, tag);
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
        Coq_alloc_small(block, 3, tag);
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
        Coq_alloc_small(block, 4, tag);
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
          if (index == Closure_tag) index = 0;
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
          accu = Field(accu, 2); // Save atom to accu register
          switch (Tag_val(accu)) {
          case ATOM_COFIX_TAG: // We are forcing a cofix
            {
              mlsize_t i, nargs;
              sp -= 2;
              // Push the current instruction as the return address
              sp[0] = StoreRA(pc - 1);
              sp[1] = coq_env;
              coq_env = Field(accu, 0); // Pointer to suspension
              accu = sp[2]; // Save accumulator to accu register
              sp[2] = Val_long(coq_extra_args); // Push number of args for return
              nargs = Wosize_val(accu) - 3; // Number of args = size of accumulator - 2 (accumulator closure) - 1 (atom)
              // Push arguments to stack
              CHECK_STACK(nargs + 1);
              sp -= nargs;
              for (i = 0; i < nargs; ++i) sp[i] = Field(accu, i + 3);
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
              int index = *pc++;
              /* Create atom */
              Coq_alloc_small(accu, 2, ATOM_PROJ_TAG);
              Field(accu, 0) = Val_int(index);
              Field(accu, 1) = *sp++;
              /* Create accumulator */
              Coq_alloc_small(block, 3, Closure_tag);
              Code_val(block) = accumulate;
              Field(block, 1) = Val_int(2);
              Field(block, 2) = accu;
              accu = block;
            }
          }
        } else {
          accu = Field(accu, *pc);
          pc++;
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
        mlsize_t i, size, sz;
        print_instr("ACCUMULATE");
        size = Wosize_val(coq_env);
        sz = size + coq_extra_args + 1;
        if (sz <= Max_young_wosize) {
          Coq_alloc_small(accu, sz, Closure_tag);
          for (i = 0; i < size; ++i)
            Field(accu, i) = Field(coq_env, i);
          for (i = size; i < sz; ++i)
            Field(accu, i) = *sp++;
        } else {
          // too large for Alloc_small, so use caml_alloc_shr instead
          // it never triggers a GC, so no need for Setup_for_gc
          accu = caml_alloc_shr(sz, Closure_tag);
          for (i = 0; i < size; ++i)
            caml_initialize(&Field(accu, i), Field(coq_env, i));
          for (i = size; i < sz; ++i)
            caml_initialize(&Field(accu, i), *sp++);
        }
        pc = LoadRA(sp[0]);
        coq_env = sp[1];
        coq_extra_args = Long_val(sp[2]);
        sp += 3;
        Next;
      }
      Instruct(MAKESWITCHBLOCK) {
        print_instr("MAKESWITCHBLOCK");
        *--sp = accu; // Save matched block on stack
        accu = Field(accu, 2); // Save atom to accu register
        switch (Tag_val(accu)) {
        case ATOM_COFIX_TAG: // We are forcing a cofix
          {
            mlsize_t i, nargs;
            print_instr("COFIX_TAG");
            sp-=2;
            pc++;
            // Push the return address
            sp[0] = StoreRA(pc + *pc);
            sp[1] = coq_env;
            coq_env = Field(accu,0); // Pointer to suspension
            accu = sp[2]; // Save accumulator to accu register
            sp[2] = Val_long(coq_extra_args); // Push number of args for return
            nargs = Wosize_val(accu) - 3; // Number of args = size of accumulator - 2 (accumulator closure) - 1 (atom)
            // Push arguments to stack
            CHECK_STACK(nargs+1);
            sp -= nargs;
            for (i = 0; i < nargs; i++) sp[i] = Field(accu, i + 3);
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
            value block;
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
              Coq_alloc_small(accu, sz, Default_tag);
              if (Is_tailrec_switch(*sp)) {
                for (i = 0; i < sz; i++) Field(accu, i) = sp[i+2];
              }else{
                for (i = 0; i < sz; i++) Field(accu, i) = sp[i+5];
              }
            }
            *--sp = accu;
            /* Create bytecode wrappers */
            Coq_alloc_small(accu, 1, Abstract_tag);
            Code_val(accu) = typlbl;
            *--sp = accu;
            Coq_alloc_small(accu, 1, Abstract_tag);
            Code_val(accu) = swlbl;
            /* We create the switch zipper */
            Coq_alloc_small(block, 5, Default_tag);
            Field(block, 0) = sp[0];
            Field(block, 1) = accu;
            Field(block, 2) = sp[2];
            Field(block, 3) = sp[1];
            Field(block, 4) = coq_env;
            sp += 3;
            accu = block;
            /* We create the atom */
            Coq_alloc_small(block, 2, ATOM_SWITCH_TAG);
            Field(block, 0) = *sp++;
            Field(block, 1) = accu;
            accu = block;
            /* We create the accumulator */
            Coq_alloc_small(block, 3, Closure_tag);
            Code_val(block) = accumulate;
            Field(block, 1) = Val_int(2);
            Field(block, 2) = accu;
            accu = block;
          }
        }
        Next;
      }



      Instruct(MAKEACCU) {
        mlsize_t i, sz;
        print_instr("MAKEACCU");
        sz = coq_extra_args + 4;
        if (sz <= Max_young_wosize) {
          Coq_alloc_small(accu, sz, Closure_tag);
          Field(accu, 2) = Field(coq_atom_tbl, *pc);
          for (i = 3; i < sz; ++i)
            Field(accu, i) = *sp++;
        } else {
          // too large for Alloc_small, so use caml_alloc_shr instead
          // it never triggers a GC, so no need for Setup_for_gc
          accu = caml_alloc_shr(sz, Closure_tag);
          caml_initialize(&Field(accu, 2), Field(coq_atom_tbl, *pc));
          for (i = 3; i < sz; ++i)
            caml_initialize(&Field(accu, i), *sp++);
        }
        Code_val(accu) = accumulate;
        Field(accu, 1) = Val_int(2);
        pc = LoadRA(sp[0]);
        coq_env = sp[1];
        coq_extra_args = Long_val(sp[2]);
        sp += 3;
        Next;
      }

      Instruct(BRANCH) {
        /* unconditional branching */
        print_instr("BRANCH");
        pc += *pc;
        /* pc = (code_t)(pc+*pc); */
        Next;
      }

      Instruct(CHECKADDINT63){
        print_instr("CHECKADDINT63");
        CheckInt2();
        /* Adds the integer in the accumulator with
           the one ontop of the stack (which is poped)*/
        Uint63_add(accu, *sp++);
        Next;
      }

      Instruct (CHECKADDCINT63) {
        print_instr("CHECKADDCINT63");
        CheckInt2();
        /* returns the sum with a carry */
        int c;
        Uint63_add(accu, *sp);
        Uint63_lt(c, accu, *sp);
        Swap_accu_sp;
        AllocCarry(c);
        Field(accu, 0) = *sp++;
        Next;
      }

      Instruct (CHECKADDCARRYCINT63) {
        print_instr("ADDCARRYCINT63");
        CheckInt2();
        /* returns the sum plus one with a carry */
        int c;
        Uint63_addcarry(accu, *sp);
        Uint63_leq(c, accu, *sp);
        Swap_accu_sp;
        AllocCarry(c);
        Field(accu, 0) = *sp++;
        Next;
      }

      Instruct (CHECKSUBINT63) {
        print_instr("CHECKSUBINT63");
        CheckInt2();
        /* returns the subtraction */
        Uint63_sub(accu, *sp++);
        Next;
      }

      Instruct (CHECKSUBCINT63) {
        print_instr("SUBCINT63");
        CheckInt2();
        /* returns the subtraction with a carry */
        int c;
        Uint63_lt(c, accu, *sp);
        Uint63_sub(accu, *sp);
        Swap_accu_sp;
        AllocCarry(c);
        Field(accu, 0) = *sp++;
        Next;
      }

      Instruct (CHECKSUBCARRYCINT63) {
        print_instr("SUBCARRYCINT63");
        CheckInt2();
        /* returns the subtraction minus one with a carry */
        int c;
        Uint63_leq(c,accu,*sp);
        Uint63_subcarry(accu,*sp);
        Swap_accu_sp;
        AllocCarry(c);
        Field(accu, 0) = *sp++;
        Next;
      }

      Instruct (CHECKMULINT63) {
        print_instr("MULINT63");
        CheckInt2();
        /* returns the multiplication */
        Uint63_mul(accu,*sp++);
        Next;
      }

      Instruct (CHECKMULCINT63) {
        /*returns the multiplication on a pair */
        print_instr("MULCINT63");
        CheckInt2();
        Uint63_mulc(accu, *sp, sp);
        *--sp = accu;
        AllocPair();
        Field(accu, 1) = *sp++;
        Field(accu, 0) = *sp++;
        Next;
      }

      Instruct(CHECKDIVINT63) {
        print_instr("CHEKDIVINT63");
        CheckInt2();
        /* spiwack: a priori no need of the NON_STANDARD_DIV_MOD flag
                    since it probably only concerns negative number.
                    needs to be checked at this point */
        int b;
        Uint63_eq0(b, *sp);
        if (b) {
          accu = *sp++;
        }
        else {
          Uint63_div(accu, *sp++);
        }
        Next;
      }

      Instruct(CHECKMODINT63) {
        print_instr("CHEKMODINT63");
        CheckInt2();
        int b;
        Uint63_eq0(b, *sp);
        if (b) {
          sp++;
        }
        else {
          Uint63_mod(accu,*sp++);
        }
        Next;
      }

      Instruct (CHECKDIVEUCLINT63) {
        print_instr("DIVEUCLINT63");
        CheckInt2();
        /* spiwack: a priori no need of the NON_STANDARD_DIV_MOD flag
                    since it probably only concerns negative number.
                    needs to be checked at this point */
        int b;
        Uint63_eq0(b, *sp);
        if (b) {
          value block;
          Coq_alloc_small(block, 2, coq_tag_pair);
          Field(block, 0) = *sp++;
          Field(block, 1) = accu;
          accu = block;
        }
        else {
          *--sp = accu;
          Uint63_div(sp[0],sp[1]);
          Swap_accu_sp;
          Uint63_mod(accu,sp[1]);
          sp[1] = sp[0];
          Swap_accu_sp;
          AllocPair();
          Field(accu, 0) = sp[1];
          Field(accu, 1) = sp[0];
          sp += 2;
        }
        Next;
      }

      Instruct(CHECKDIVSINT63) {
        print_instr("CHEKDIVSINT63");
        CheckInt2();
        int b;
        Uint63_eq0(b, *sp);
        if (b) {
          accu = *sp++;
        }
        else {
          Uint63_eqm1(b, *sp);
          if (b) {
            Uint63_neg(accu);
            sp++;
          }
          else {
            Uint63_divs(accu, *sp++);
          }
        }
        Next;
      }

      Instruct(CHECKMODSINT63) {
        print_instr("CHEKMODSINT63");
        CheckInt2();
        int b;
        Uint63_eq0(b, *sp);
        if (b) {
          sp++;
        }
        else {
          Uint63_mods(accu,*sp++);
        }
        Next;
      }

      Instruct (CHECKDIV21INT63) {
        print_instr("DIV21INT63");
        CheckInt3();
        Uint63_div21(accu, sp[0], sp[1], &(sp[1]));
        Swap_accu_sp;
        AllocPair();
        Field(accu, 0) = sp[1];
        Field(accu, 1) = sp[0];
        sp += 2;
        Next;
      }

      Instruct(CHECKLXORINT63) {
        print_instr("CHECKLXORINT63");
        CheckInt2();
        Uint63_lxor(accu,*sp++);
        Next;
      }

      Instruct(CHECKLORINT63) {
        print_instr("CHECKLORINT63");
        CheckInt2();
        Uint63_lor(accu,*sp++);
        Next;
      }

      Instruct(CHECKLANDINT63) {
        print_instr("CHECKLANDINT63");
        CheckInt2();
        Uint63_land(accu,*sp++);
        Next;
      }

      Instruct(CHECKLSLINT63) {
        print_instr("CHECKLSLINT63");
        CheckInt2();
        Uint63_lsl(accu,*sp++);
        Next;
      }

      Instruct(CHECKLSRINT63) {
        print_instr("CHECKLSRINT63");
        CheckInt2();
        Uint63_lsr(accu,*sp++);
        Next;
      }

      Instruct(CHECKASRINT63) {
        print_instr("CHECKASRINT63");
        CheckInt2();
        Uint63_asr(accu,*sp++);
        Next;
      }

      Instruct (CHECKADDMULDIVINT63) {
        print_instr("CHECKADDMULDIVINT63");
        CheckInt3();
        Uint63_addmuldiv(accu,sp[0],sp[1]);
        sp += 2;
        Next;
      }

      Instruct (CHECKEQINT63) {
        print_instr("CHECKEQINT63");
        CheckInt2();
        int b;
        Uint63_eq(b, accu, *sp++);
        accu = b ? coq_true : coq_false;
        Next;
      }

     Instruct (CHECKLTINT63) {
        print_instr("CHECKLTINT63");
        CheckInt2();
       int b;
       Uint63_lt(b,accu,*sp++);
       accu = b ? coq_true : coq_false;
       Next;
     }

     Instruct (CHECKLEINT63) {
       print_instr("CHECKLEINT63");
       CheckInt2();
       int b;
       Uint63_leq(b,accu,*sp++);
       accu = b ? coq_true : coq_false;
       Next;
     }

     Instruct (CHECKLTSINT63) {
       print_instr("CHECKLTSINT63");
       CheckInt2();
       int b;
       Uint63_lts(b,accu,*sp++);
       accu = b ? coq_true : coq_false;
       Next;
     }

     Instruct (CHECKLESINT63) {
       print_instr("CHECKLESINT63");
       CheckInt2();
       int b;
       Uint63_les(b,accu,*sp++);
       accu = b ? coq_true : coq_false;
       Next;
     }

     Instruct (CHECKCOMPAREINT63) {
        /* returns Eq if equal, Lt if accu is less than *sp, Gt otherwise */
        /* assumes Inductive _ : _ := Eq | Lt | Gt */
        print_instr("CHECKCOMPAREINT63");
        CheckInt2();
        int b;
        Uint63_eq(b, accu, *sp);
        if (b) {
          accu = coq_Eq;
          sp++;
        }
        else {
          Uint63_lt(b, accu, *sp++);
          accu = b ? coq_Lt : coq_Gt;
        }
        Next;
      }

     Instruct (CHECKCOMPARESINT63) {
       /* returns Eq if equal, Lt if accu is less than *sp, Gt otherwise */
       /* assumes Inductive _ : _ := Eq | Lt | Gt */
       print_instr("CHECKCOMPARESINT63");
       CheckInt2();
       int b;
       Uint63_eq(b, accu, *sp);
       if (b) {
         accu = coq_Eq;
         sp++;
       }
       else {
         Uint63_lts(b, accu, *sp++);
         accu = b ? coq_Lt : coq_Gt;
       }
       Next;
     }

      Instruct (CHECKHEAD0INT63) {
        print_instr("CHECKHEAD0INT63");
        CheckInt1();
        Uint63_head0(accu);
        Next;
      }

      Instruct (CHECKTAIL0INT63) {
        print_instr("CHECKTAIL0INT63");
        CheckInt1();
        Uint63_tail0(accu);
        Next;
      }

      Instruct (CHECKOPPFLOAT) {
        print_instr("CHECKOPPFLOAT");
        CheckFloat1();
        Coq_copy_double(-Double_val(accu));
        Next;
      }

      Instruct (CHECKABSFLOAT) {
        print_instr("CHECKABSFLOAT");
        CheckFloat1();
        Coq_copy_double(fabs(Double_val(accu)));
        Next;
      }

      Instruct (CHECKEQFLOAT) {
        print_instr("CHECKEQFLOAT");
        CheckFloat2();
        accu = Double_val(accu) == Double_val(*sp++) ? coq_true : coq_false;
        Next;
      }

      Instruct (CHECKLTFLOAT) {
        print_instr("CHECKLTFLOAT");
        CheckFloat2();
        accu = Double_val(accu) < Double_val(*sp++) ? coq_true : coq_false;
        Next;
      }

      Instruct (CHECKLEFLOAT) {
        print_instr("CHECKLEFLOAT");
        CheckFloat2();
        accu = Double_val(accu) <= Double_val(*sp++) ? coq_true : coq_false;
        Next;
      }

      Instruct (CHECKCOMPAREFLOAT) {
        double x, y;
        print_instr("CHECKCOMPAREFLOAT");
        CheckFloat2();
        x = Double_val(accu);
        y = Double_val(*sp++);
        if(x < y) {
          accu = coq_FLt;
        }
        else if(x > y) {
          accu = coq_FGt;
        }
        else if(x == y) {
          accu = coq_FEq;
        }
        else { // nan value
          accu = coq_FNotComparable;
        }
        Next;
      }

      Instruct (CHECKCLASSIFYFLOAT) {
        double x;
        print_instr("CHECKCLASSIFYFLOAT");
        CheckFloat1();
        x = Double_val(accu);
        switch (fpclassify(x)) {
        case FP_NORMAL:
          accu = signbit(x) ? coq_NNormal : coq_PNormal;
          break;
        case FP_SUBNORMAL:
          accu = signbit(x) ? coq_NSubn : coq_PSubn;
          break;
        case FP_ZERO:
          accu = signbit(x) ? coq_NZero : coq_PZero;
          break;
        case FP_INFINITE:
          accu = signbit(x) ? coq_NInf : coq_PInf;
          break;
        default:  /* FP_NAN */
          accu = coq_NaN;
          break;
        }
        Next;
      }

      Instruct (CHECKADDFLOAT) {
        print_instr("CHECKADDFLOAT");
        CheckFloat2();
        Coq_copy_double(Double_val(accu) + Double_val(*sp++));
        Next;
      }

      Instruct (CHECKSUBFLOAT) {
        print_instr("CHECKSUBFLOAT");
        CheckFloat2();
        Coq_copy_double(Double_val(accu) - Double_val(*sp++));
        Next;
      }

      Instruct (CHECKMULFLOAT) {
        print_instr("CHECKMULFLOAT");
        CheckFloat2();
        Coq_copy_double(Double_val(accu) * Double_val(*sp++));
        Next;
      }

      Instruct (CHECKDIVFLOAT) {
        print_instr("CHECKDIVFLOAT");
        CheckFloat2();
        Coq_copy_double(Double_val(accu) / Double_val(*sp++));
        Next;
      }

      Instruct (CHECKSQRTFLOAT) {
        print_instr("CHECKSQRTFLOAT");
        CheckFloat1();
        Coq_copy_double(sqrt(Double_val(accu)));
        Next;
      }

      Instruct (CHECKFLOATOFINT63) {
        print_instr("CHECKFLOATOFINT63");
        CheckInt1();
        Uint63_to_double(accu);
        Next;
      }

      Instruct (CHECKFLOATNORMFRMANTISSA) {
        double f;
        print_instr("CHECKFLOATNORMFRMANTISSA");
        CheckFloat1();
        f = fabs(Double_val(accu));
        if (f >= 0.5 && f < 1) {
          Uint63_of_double(ldexp(f, DBL_MANT_DIG));
        }
        else {
          Uint63_of_int(Val_int(0));
        }
        Next;
      }

      Instruct (CHECKFRSHIFTEXP) {
        int exp;
        double f;
        print_instr("CHECKFRSHIFTEXP");
        CheckFloat1();
        /* frexp(infinity) incorrectly returns nan on mingw */
#if defined(__MINGW32__) || defined(__MINGW64__)
        if (fpclassify(Double_val(accu)) == FP_INFINITE) {
          f = Double_val(accu);
        } else
#endif
        f = frexp(Double_val(accu), &exp);
        if (fpclassify(f) == FP_NORMAL) {
          exp += FLOAT_EXP_SHIFT;
        }
        else {
          exp = 0;
        }
        Coq_copy_double(f);
        *--sp = accu;
#ifdef ARCH_SIXTYFOUR
        Coq_alloc_small(accu, 2, coq_tag_pair);
        Field(accu, 1) = Val_int(exp);
#else
        Uint63_of_int(Val_int(exp));
        *--sp = accu;
        Coq_alloc_small(accu, 2, coq_tag_pair);
        Field(accu, 1) = *sp++;
#endif
        Field(accu, 0) = *sp++;
        Next;
      }

      Instruct (CHECKLDSHIFTEXP) {
        print_instr("CHECKLDSHIFTEXP");
        CheckPrimArgs(Is_double(accu) && Is_uint63(sp[0]), apply2);
        Swap_accu_sp;
        Uint63_to_int_min(accu, Val_int(2 * FLOAT_EXP_SHIFT));
        accu = Int_val(accu);
        Coq_copy_double(ldexp(Double_val(*sp++), accu - FLOAT_EXP_SHIFT));
        Next;
      }

      Instruct (CHECKNEXTUPFLOAT) {
        print_instr("CHECKNEXTUPFLOAT");
        CheckFloat1();
        Coq_copy_double(coq_next_up(Double_val(accu)));
        Next;
      }

      Instruct (CHECKNEXTDOWNFLOAT) {
        print_instr("CHECKNEXTDOWNFLOAT");
        CheckFloat1();
        Coq_copy_double(coq_next_down(Double_val(accu)));
        Next;
      }

      Instruct (CHECKNEXTUPFLOATINPLACE) {
        print_instr("CHECKNEXTUPFLOATINPLACE");
        CheckFloat1();
        Store_double_val(accu, coq_next_up(Double_val(accu)));
        Next;
      }

      Instruct (CHECKNEXTDOWNFLOATINPLACE) {
        print_instr("CHECKNEXTDOWNFLOATINPLACE");
        CheckFloat1();
        Store_double_val(accu, coq_next_down(Double_val(accu)));
        Next;
      }

      Instruct(CHECKCAMLCALL2_1) {
        // arity-2 callback, the last argument can be an accumulator
        value arg;
        print_instr("CHECKCAMLCALL2_1");
        if (!Is_accu(accu)) {
          pc++;
          print_int(*pc);
          arg = sp[0];
          Setup_for_caml_call;
          accu = caml_callback2(Field(coq_global_data, *pc), accu, arg);
          Restore_after_caml_call;
          sp += 1;
          pc++;
        } else pc += *pc;
        Next;
      }

      Instruct(CHECKCAMLCALL1) {
        // arity-1 callback, no argument can be an accumulator
        print_instr("CHECKCAMLCALL1");
        if (!Is_accu(accu)) {
          pc++;
          Setup_for_caml_call;
          print_int(*pc);
          accu = caml_callback(Field(coq_global_data, *pc), accu);
          Restore_after_caml_call;
          pc++;
        }
        else pc += *pc;
        Next;
      }

      Instruct(CHECKCAMLCALL2) {
        // arity-2 callback, no argument can be an accumulator
        value arg;
        print_instr("CHECKCAMLCALL2");
        if (!Is_accu(accu) && !Is_accu(sp[0])) {
          pc++;
          arg = sp[0];
          Setup_for_caml_call;
          print_int(*pc);
          accu = caml_callback2(Field(coq_global_data, *pc), accu, arg);
          Restore_after_caml_call;
          sp += 1;
          pc++;
        } else pc += *pc;
        Next;
      }

      Instruct(CHECKCAMLCALL3_1) {
        // arity-3 callback, the last argument can be an accumulator
        value arg1;
        value arg2;
        print_instr("CHECKCAMLCALL3_1");
        if (!Is_accu(accu) && !Is_accu(sp[0])) {
          pc++;
          arg1 = sp[0];
          arg2 = sp[1];
          Setup_for_caml_call;
          print_int(*pc);
          accu = caml_callback3(Field(coq_global_data, *pc), accu, arg1, arg2);
          Restore_after_caml_call;
          sp += 2;
          pc++;
        } else pc += *pc;
        Next;
      }

/* Debugging and machine control */

      Instruct(STOP){
        print_instr("STOP");
        coq_sp = sp;
        CAMLreturn(accu);
      }


#ifndef THREADED_CODE
    default:
      /*fprintf(stderr, "%d\n", *pc);*/
      caml_failwith("Coq VM: Fatal error: bad opcode");
    }
  }
#endif
}

value coq_push_ra(value code) {
  code_t tcode = Code_val(code);
  print_instr("push_ra");
  coq_sp -= 3;
  coq_sp[0] = StoreRA(tcode);
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
  nargs = Wosize_val(args) - 3;
  CHECK_STACK(nargs);
  coq_sp -= nargs;
  print_instr("push_args");print_int(nargs);
  for (i = 0; i < nargs; i++) coq_sp[i] = Field(args, i + 3);
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
  CHECK_STACK(uint_of_value(max_stack_size));
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
