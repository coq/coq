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

CAMLprim value win32_kill(value pid) {
  CAMLparam1(pid);
  TerminateProcess((HANDLE)(Long_val(pid)), 0);
  CAMLreturn(Val_unit);
}
