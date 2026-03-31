\# Deadlock Detection using SymbiYosys



\## 1. Introduction



Deadlocks are a critical class of bugs in digital designs where the system enters a state with no possible forward progress. Detecting such issues early is important for ensuring correct system behavior.

This example demonstrates how **Formal verification** can be used to identify deadlocks in RTL designs using SymbiYosys.



\## 2. Design Overview



The design is a simple Finite State Machine (FSM) with three states: IDLE, WAIT, GRANT

State Transitions:

\- From 'IDLE', the FSM moves to 'WAIT' when 'req' is asserted.

\- The 'WAIT' state has no outgoing transitions.

\- The 'GRANT' state is never reached.

This creates a Deadlock condition, where the FSM gets stuck in the 'WAIT' state indefinitely.



\## 3. Deadlock Scenario



IDLE --(req)--> WAIT --(no exit)--> WAIT (forever)

Once the FSM enters the 'WAIT' state, it cannot transition to any other state.



\## 4. Formal Verification Approach



Instead of simulating specific test cases, formal verification explores all possible behaviors of the design.

Property Used: cover(grant);



\## 5. Interpretation of Results

If the cover condition is reached -> the GRANT state is reachable (no deadlock)

If the cover condition is not reached -> the GRANT state is unreachable

In this design, The GRANT state is never reached. Therefore, the FSM is deadlocked



\##6. Running the Example

Requirements:

Yosys

SymbiYosys

Run Command: sby -f deadlock.sby



\## 7. Expected Outcome



Status: PASSED

This indicates that the cover condition (grant = 1) was not reached, implying that the GRANT state is unreachable.



Status: UNKNOWN

This indicates that the tool could not fully determine the result within the given exploration depth.

However, since the cover condition was not reached during exploration, it still suggests that the GRANT state is likely unreachable.



Interpretation:



In both cases, the GRANT state is not reached during formal exploration.

This means there is no valid execution path that allows the FSM to progress beyond the WAIT state.



Therefore, the FSM is stuck in a state with no forward progress, indicating a deadlock condition.

