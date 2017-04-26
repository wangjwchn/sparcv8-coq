COQBIN   := $${coq86bin}
COQC     := $(strip $(COQBIN))coqc
COQDEP   := $(strip $(COQBIN))coqdep
COQWC   := $(strip $(COQBIN))coqwc

SUBDIRS :=

COQFLAGS :=

SRCFILES := $(shell find $(SUBDIRS) -type f -name "*.v")
OBJFILES := $(patsubst %.v, %.vo, $(SRCFILES))
QOBJFILES := $(patsubst %.v, %.vio, $(SRCFILES))
DEPFILES := $(join $(dir $(SRCFILES)),$(addprefix ., $(addsuffix .d,$(notdir $(SRCFILES)))))

all: $(OBJFILES)

quick: $(QOBJFILES)

version: 
	$(COQC) --version

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

%.vio: %.v
	$(COQC) $(COQFLAGS) $< -quick

clean:
	find . -type f -name "*.vo" -delete
	find . -type f -name "*.glob" -delete
	find . -type f -name "*.d" -delete
	find . -type f -name "*.vio" -delete
	rm -f .deps

wc:
	$(COQWC) $(SRCFILES)

#deps: .deps

#.deps: $(SRCFILES)
#	$(COQDEP) $(COQFLAGS) $(SRCFILES) > $@

.%.v.d: %.v
	$(COQDEP) $(COQFLAGS) "$<" > "$@" 

-include $(DEPFILES)
.SECONDARY: $(DEPFILES)

.PHONY: wc
