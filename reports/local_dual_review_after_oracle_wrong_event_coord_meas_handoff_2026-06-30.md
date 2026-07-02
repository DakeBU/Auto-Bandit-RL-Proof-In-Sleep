# Local Dual-Agent Review Handoff: After Oracle Wrong-Event Coordinate Measurability

Current review prompt:

```bash
python3 tools\bandit.py review-prompt
```

When route judgment is needed:

1. Spawn two local agents with distinct review responsibilities.
2. Ask one agent to review Lean/API feasibility and smallest compilable next
   step.
3. Ask the other agent to review mathematical dependency order and downstream
   proof risk.
4. Combine their advice in a local review artifact.
5. Record the decision with:

```bash
python3 tools\bandit.py review-record-response --raw RAW --output reports\local_dual_review_after_oracle_wrong_event_coord_meas_decision_2026-06-30.md --chosen-leaf CHOSEN --classification CLASSIFICATION
```

Do not use ChatGPT Extended Pro as a required gate for current work.
