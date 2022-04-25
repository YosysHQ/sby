test:
	@$(MAKE) -C .. $(SUBDIR)/$@

.PHONY: test refresh IMPLICIT_PHONY

IMPLICIT_PHONY:

refresh:
	@$(MAKE) -C .. refresh

help:
	@$(MAKE) -C .. help

%: IMPLICIT_PHONY
	@$(MAKE) -C .. $(SUBDIR)/$@
