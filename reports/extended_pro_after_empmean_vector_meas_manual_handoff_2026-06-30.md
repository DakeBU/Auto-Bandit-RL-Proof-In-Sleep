# Manual Extended Pro Handoff: After EmpMean Vector Measurability Bridge

Use this if browser automation is unavailable.

1. Open ChatGPT with Extended Pro / high reasoning.
2. Submit:
   `reports/extended_pro_after_empmean_vector_meas_candidate_prompt_2026-06-30.md`
3. Wait for the response to finish. Do not duplicate the prompt.
4. Save the raw response as:
   `reports/extended_pro_after_empmean_vector_meas_raw_2026-06-30.md`
5. Record it with:

```powershell
python3 tools\bandit.py extended-pro-record-response --raw reports\extended_pro_after_empmean_vector_meas_raw_2026-06-30.md --output reports\extended_pro_after_empmean_vector_meas_response_2026-06-30.md --url URL --chosen-leaf CHOSEN --classification CLASSIFICATION
```

6. Run:

```powershell
python3 tools\bandit.py review-status --json
python3 tools\bandit.py check
```
