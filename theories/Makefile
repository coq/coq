.PHONY: stdlib-cm

BUILD_DIR=$(shell pwd)/../_build_vo/default

COQMAKEFILE:=$(BUILD_DIR)/bin/coq_makefile

LOCAL_FILE:=Makefile.coq.local

export COQBIN=$(BUILD_DIR)/bin
export COQLIB=$(BUILD_DIR)/lib/coq

# Missing dep on coqc
stdlib-cm: $(LOCAL_FILE) Makefile.coq
	echo $(COQSRCLIBS)
	$(MAKE) -f Makefile.coq Init/Prelude.vo
	$(MAKE) -f Makefile.coq

# Missing dep on coq_makefile
Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $@
