Staged simulation + verification example demonstrating staged verification using simulation and writeback via `sim -w` pass.
- Stage 1: run cover to reach “req sent, ack pending”, producing `trace0.yw`.
- Stage 2: replay the witness with `sim -w` to bake state, then run another cover that requires the ack.
- Uses phased SVA (`(* phase = "1" *)`, `(* phase = "2" *)`) and a selector script to strip irrelevant properties per stage.
- Needs Yosys with Verific (`verific -formal` in the scripts).

Run via the wrapper: from the root directory, call `make -C tests staged_sim_and_verif/staged_sim_and_verif`, which calls `staged_sim_and_verif.sh` and exercises all four tasks in `skip_staged_flow.sby`.
