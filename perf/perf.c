/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

#include <linux/perf_event.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <errno.h>
#include <string.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>

static int perf_event_open(struct perf_event_attr *hw_event, pid_t pid,
                           int cpu, int group_fd, unsigned long flags) {
  return syscall(SYS_perf_event_open, hw_event, pid, cpu, group_fd, flags);
}

#define NOT_INITIALIZED (-2)

int fd = NOT_INITIALIZED;

CAMLprim value CAML_init(value unit) {
  CAMLparam1(unit);

  if (fd != NOT_INITIALIZED) {
    caml_failwith("counter already initialized");
  }

  struct perf_event_attr pe;
  memset(&pe, 0, sizeof(pe));

  pe.type = PERF_TYPE_HARDWARE;
  pe.size = sizeof(pe);
  pe.config = PERF_COUNT_HW_INSTRUCTIONS;
  pe.disabled = 1;
  pe.exclude_kernel = 1;
  pe.exclude_hv = 1;

  fd = perf_event_open(&pe, 0, -1, -1, 0);
  if (fd == -1) {
    fd = NOT_INITIALIZED;
    caml_failwith("initialisation failure");
  }

  if (ioctl(fd, PERF_EVENT_IOC_RESET , 0) == -1) {
    close(fd);
    fd = NOT_INITIALIZED;
    caml_failwith("could not initially reset counter");
  }

  if (ioctl(fd, PERF_EVENT_IOC_ENABLE, 0) == -1) {
    close(fd);
    fd = NOT_INITIALIZED;
    caml_failwith("could not initailly enable counter");
  }

  CAMLreturn(Val_unit);
}

CAMLprim value CAML_drop(value unit) {
  CAMLparam1(unit);

  if (fd == NOT_INITIALIZED) {
    caml_failwith("counter not initialized");
  }

  close(fd);
  fd = NOT_INITIALIZED;

  CAMLreturn(Val_unit);
}

CAMLprim value CAML_peek(value unit) {
  CAMLparam1(unit);

  if (fd == NOT_INITIALIZED) caml_failwith("counter not initialized");

  if (ioctl(fd, PERF_EVENT_IOC_DISABLE, 0) == -1) {
    caml_failwith("could not disable counter");
  }

  int64_t count = 0;
  size_t n = read(fd, &count, sizeof(count));

  if (n != sizeof(count)) {
    caml_failwith("could not retrieve counter");
  }

  value ret = caml_copy_int64(count);

  if (ioctl(fd, PERF_EVENT_IOC_ENABLE, 0) == -1) {
    caml_failwith("could not enable counter");
  }

  CAMLreturn(ret);
}
