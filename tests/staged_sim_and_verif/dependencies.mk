skip_staged_flow_%: skip_staged_flow.sby
	sby -f skip_staged_flow.sby $*
	
skip_staged_flow_stage_1: skip_staged_flow_prep
skip_staged_flow_stage_2: skip_staged_flow_stage_1
skip_staged_flow_stage_3_init: skip_staged_flow_stage_2
skip_staged_flow_stage_3a_cover skip_staged_flow_stage_3b_assert: skip_staged_flow_stage_3_init

.PHONY: stage_3
stage_3: skip_staged_flow_stage_3a_cover skip_staged_flow_stage_3b_assert

.PHONY: clean
clean:
	@rm -rf skip_staged_flow
	@rm -rf skip_staged_flow_*
