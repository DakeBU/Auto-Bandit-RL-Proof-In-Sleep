# Manual Extended Pro Handoff: After Coarse ETC Suffix Regret Bound

Use this if browser submission is unavailable.

1. Run:

   ```powershell
   python3 tools\bandit.py extended-pro-prompt
   ```

2. Submit the printed prompt to ChatGPT Extended Pro.

3. Save the raw answer and record it with:

   ```powershell
   python3 tools\bandit.py extended-pro-record-response --raw PATH --output reports\extended_pro_after_coarse_suffix_regret_response_2026-06-30.md
   ```

4. Verify:

   ```powershell
   python3 tools\bandit.py review-status --require-response
   python3 tools\bandit.py check
   ```

## Prompt File

`reports/extended_pro_after_coarse_suffix_regret_candidate_prompt_2026-06-30.md`
