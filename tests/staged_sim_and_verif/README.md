Staged simulation + verification example demonstrating staged verification using simulation and writeback via `sim -w` pass.
- Stage 1: run cover to reach “req sent, ack pending”, producing `trace0.yw`.
- Stage 2: replay the witness with `sim -w` to bake state, then run another cover that requires the ack.
- Uses phased SVA (`(* phase = "1" *)`, `(* phase = "2" *)`) and a selector script to strip irrelevant properties per stage.
- Needs Yosys with Verific (`verific -formal` in the scripts).

Run via the wrapper: from the root directory, call `make -C tests staged_sim_and_verif/staged_sim_and_verif`, which calls `staged_sim_and_verif.sh` and exercises all four tasks in `skip_staged_flow.sby`. You may also run each task manually; simply ensure you run the tasks in the correct order shown in the `.sh` file.

Design notes
- Two-phase flow: phase 1 reaches “two reqs seen” and emits a witness; phase 2 replays that witness with `sim -w` and covers the matching ack.
- Phase separation uses labeled properties (`phase1_*` / `phase2_*`), matching the SCY approach; each phase prunes with `select */c:phase* */c:phase1_* %d` (or `phase2_*`) then `delete`, leaving only the desired phase’s properties.
- Tooling: needs Yosys with Verific (`verific -formal`) for SVA parsing. The minimal `staged_sim_and_verif.sby` exists just so the test harness discovers the Verific requirement.
- Harness glue: the current make harness can’t express “run these SBY tasks sequentially from one .sby”; it spins each task as an independent target. We keep the multi-task config in `skip_staged_flow.sby` (prefixed so collect skips it) and use `staged_sim_and_verif.sh` to drive the four tasks in order. The tiny `staged_sim_and_verif.sby` is only there so collect/required_tools see the test; the `.sh` enforces ordering. Set `SBY_MAIN` to your SBY entrypoint (e.g., `.../share/yosys/python3/sby_cmdline.py` from OSS CAD Suite) when running manually.
