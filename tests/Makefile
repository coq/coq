all: $(patsubst %.v,%.v.log,$(wildcard *.v))

%.v.log: %.v
	$(COQBIN)/coqtop -I ../src -Q ../theories Ltac2 < $< 2> $@

clean:
	rm -f *.log
