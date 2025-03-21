ifeq "$(ROCQBIN)" ""
  ROCQBIN=$(dir $(shell which rocq))/
endif

%: Makefile.rocq

Makefile.rocq: _CoqProject
	$(ROCQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

-include Makefile.rocq
