Staged simulation + verification example demonstrating staged verification using simulation and writeback via `sim -w` pass.

This test mirrors what is described in <https://yosyshq.readthedocs.io/projects/ap130/en/latest/>, and should be kept up to date with that appnote.

- Stage 1: run cover to reach “req sent, ack pending”, producing `trace0.yw`.
- Stage 2A (cover branch): replay the witness with `sim -w` to bake state, then run another cover that requires the ack.
- Stage 2B (assert branch): replay the same baked state and assert there is at most one further ack after the second req.
- Uses labeled properties (`phase1_*`, `phase2_shared_*`, `phase2a_*`, `phase2b_*`) and a selector script to strip irrelevant properties per stage.
- Needs Yosys with Verific (`verific -formal` in the scripts).

Run via the wrapper: from the root directory, call `make -C tests staged_sim_and_verif/staged_sim_and_verif`, which calls `staged_sim_and_verif.sh` and exercises all five tasks in `skip_staged_flow.sby`. You may also run each task manually; simply ensure you run the tasks in the correct order shown in the `.sh` file.

Design notes
- Two-phase flow with a branch in phase 2: phase 1 reaches “two reqs seen” and emits a witness; phase 2 replays that witness with `sim -w` and then splits into a cover branch (ack) and an assert branch (single remaining ack). This covers both SCY-like sequential covers and an assertion path that goes beyond SCY’s current cover-only sequencing.
- Phase separation uses labeled properties (`phase1_*`, `phase2_shared_*`, `phase2a_*`, `phase2b_*`), matching the SCY approach. Each branch prunes with `select */c:phase* ... %u %d` to keep only the shared + branch-specific labels for that task.
- Tooling: needs Yosys with Verific (`verific -formal`) for SVA parsing. The minimal `staged_sim_and_verif.sby` exists just so the test harness discovers the Verific requirement.
- Harness glue: the current make harness can’t express “run these SBY tasks sequentially from one .sby”; it spins each task as an independent target. We keep the multi-task config in `skip_staged_flow.sby` (prefixed so collect skips it) and use `staged_sim_and_verif.sh` to drive the five tasks in order. The tiny `staged_sim_and_verif.sby` is only there so collect/required_tools see the test and recognize that verific is required. The `.sh` is what actually runs and enforces ordering.
