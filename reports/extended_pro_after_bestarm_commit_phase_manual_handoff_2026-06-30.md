# Manual Extended Pro Handoff: After ETC BestArm Commit Phase

Use this only if the in-app browser handoff fails.

1. Run:

   ```powershell
   python3 tools\bandit.py extended-pro-prompt
   ```

2. Paste the printed prompt into ChatGPT Extended Pro.
3. Save the raw answer to a local text file.
4. Record the completed response:

   ```powershell
   python3 tools\bandit.py extended-pro-record-response --raw PATH --output reports\extended_pro_after_bestarm_commit_phase_response_2026-06-30.md --url URL --chosen-leaf CHOSEN --classification project-local
   ```

5. Verify:

   ```powershell
   python3 tools\bandit.py review-status --json
   python3 tools\bandit.py check
   ```

Prompt file:

`reports/extended_pro_after_bestarm_commit_phase_candidate_prompt_2026-06-30.md`
