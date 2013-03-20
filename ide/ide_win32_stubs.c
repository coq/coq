#define _WIN32_WINNT 0x0501  /* Cf below, we restrict to  */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <windows.h>

/* Win32 emulation of kill -9 */

/* The pid returned by Unix.create_process is actually a pseudo-pid,
   made via a cast of the obtained HANDLE, (cf. win32unix/createprocess.c
   in the sources of ocaml). Since we're still in the caller process,
   we simply cast back to get an handle...
   The 0 is the exit code we want for the terminated process.
*/

CAMLprim value win32_kill(value pseudopid) {
  CAMLparam1(pseudopid);
  TerminateProcess((HANDLE)(Long_val(pseudopid)), 0);
  CAMLreturn(Val_unit);
}

/* Win32 emulation of a kill -2 (SIGINT) */

/* For simplicity, we signal all processes sharing a console with coqide.
   This shouldn't be an issue since currently at most one coqtop is busy
   at a given time. Earlier, we tried to be more precise via
   FreeConsole and AttachConsole before generating the Ctrl-C, but
   that wasn't working so well (see #2869).
   This code rely now on the fact that coqide is a console app,
   and that coqide itself ignores Ctrl-C.
*/

CAMLprim value win32_interrupt_all(value unit) {
  CAMLparam1(unit);
  GenerateConsoleCtrlEvent(CTRL_C_EVENT,0);
  CAMLreturn(Val_unit);
}

/* Get rid of the nasty console window (only if we created it) */

CAMLprim value win32_hide_console (value unit) {
  CAMLparam1(unit);
  DWORD pid;
  HWND hw = GetConsoleWindow();
  if (hw != NULL) {
    GetWindowThreadProcessId(hw, &pid);
    if (pid == GetCurrentProcessId())
      ShowWindow(hw, SW_HIDE);
  }
  CAMLreturn(Val_unit);
}
