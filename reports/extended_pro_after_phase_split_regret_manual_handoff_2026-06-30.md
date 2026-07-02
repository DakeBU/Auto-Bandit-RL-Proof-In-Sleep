# Manual Extended Pro Handoff: After ETC Phase-Split Regret

Use this if browser submission is unavailable.

1. Print the prompt:

   ```powershell
   python3 tools\bandit.py extended-pro-prompt
   ```

2. Submit it to ChatGPT Extended Pro.

3. Save the raw answer and record it:

   ```powershell
   python3 tools\bandit.py extended-pro-record-response --raw PATH --output reports\extended_pro_after_phase_split_regret_response_2026-06-30.md
   ```

4. Verify:

   ```powershell
   python3 tools\bandit.py review-status --require-response
   python3 tools\bandit.py check
   ```

## Prompt File

`reports/extended_pro_after_phase_split_regret_candidate_prompt_2026-06-30.md`
