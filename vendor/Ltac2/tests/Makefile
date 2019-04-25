ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which coqc))/
endif

all: $(patsubst %.v,%.v.log,$(wildcard *.v))

%.v.log: %.v
	$(COQBIN)/coqc -I ../src -Q ../theories Ltac2 $< > $@
	if [ $$? = 0 ]; then \
		echo "    $<... OK"; \
	else \
		echo "    $<... FAIL!"; \
	fi; \

clean:
	rm -f *.log
