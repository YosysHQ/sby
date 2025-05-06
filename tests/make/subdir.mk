TESTDIR ?= ..

test:
	@$(MAKE) -C $(TESTDIR) $(SUBDIR)/$@

.PHONY: test refresh IMPLICIT_PHONY

Makefile: IMPLICIT_PHONY
%.mk: IMPLICIT_PHONY

IMPLICIT_PHONY:

refresh:
	@$(MAKE) -C $(TESTDIR) refresh

help:
	@$(MAKE) -C $(TESTDIR) help

%: IMPLICIT_PHONY
	@$(MAKE) -C $(TESTDIR) $(SUBDIR)/$@
