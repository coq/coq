#include <stdio.h>
#include <sys/file.h>

#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>

CAMLprim value coq_flock(value fd, value operation)
{
  CAMLparam2 (fd, operation);

  int fd_i = Int_val(fd);
  int operation_i = Int_val(operation);

  // printf("stub_fd: %d ; op_id: %d", fd_i, operation_i);

  int operation_f = 0;

  switch (operation_i) {
  case 0:
    operation_f = LOCK_SH;
    break;
  case 1:
    operation_f = LOCK_EX;
    break;
  case 2:
    operation_f = LOCK_UN;
    break;
  default:
    caml_invalid_argument("Incorrect flock operation");
    break;
  };

  int res = flock(fd_i, operation_f);

  if (res != 0) { perror("flock: "); };
  CAMLreturn ( Val_int(res) );
}
