#define _WIN32_WINNT 0x0501  /* Cf below, we restrict to  */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <windows.h>

/* Win32 emulation of a kill -2 (SIGINT) */

/* This code rely of the fact that coqide is now without initial console.
   Otherwise, no console creation in win32unix/createprocess.c, hence
   the same console for coqide and all coqtop, and everybody will be
   signaled at the same time by the code below. */

/* Moreover, AttachConsole exists only since WinXP, and GetProcessId
   since WinXP SP1. For avoiding the GetProcessId, we could adapt code
   from win32unix/createprocess.c to make it return both the pid and the
   handle. For avoiding the AttachConsole, I don't know, maybe having
   an intermediate process between coqide and coqtop ? */

CAMLprim value win32_interrupt(value pseudopid) {
  CAMLparam1(pseudopid);
  HANDLE h;
  DWORD pid;
  FreeConsole(); /* Normally unnecessary, just to be sure... */
  h = (HANDLE)(Long_val(pseudopid));
  pid = GetProcessId(h);
  AttachConsole(pid);
  /* We want to survive the Ctrl-C that will also concerns us */
  SetConsoleCtrlHandler(NULL,TRUE); /* NULL + TRUE means ignore */
  GenerateConsoleCtrlEvent(CTRL_C_EVENT,0); /* signal our co-console */
  FreeConsole();
  CAMLreturn(Val_unit);
}
