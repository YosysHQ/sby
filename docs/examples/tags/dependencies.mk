.PHONY: stage_1 stage_2 stage_2_alt
dependencies_%: dependencies.sby
	sby -f dependencies.sby $*

STAGE_1_TARGS = dependencies_stage_1
stage_1: $(STAGE_1_TARGS)

STAGE_2_TARGS = dependencies_stage_2a dependencies_stage_2b
$(STAGE_2_TARGS): stage_1
stage_2: $(STAGE_2_TARGS)

# both tasks together
stage_2_alt: stage_1
	sby -f dependencies.sby stage_2a stage_2b
