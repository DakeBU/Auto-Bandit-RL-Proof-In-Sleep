python3 -m unittest tools.test_contributor_contract tools.test_process_memory
if [[ -n "$CONTRIBUTOR_HEAD" ]]; then
  # Provenance is checked on the contribution's real history. Keep
  # this checkout for integration tests, Lean, and documentation.
  contract_root="$RUNNER_TEMP/abrl-contributor-head"
  git worktree add --detach "$contract_root" "$CONTRIBUTOR_HEAD"
  python3 "$contract_root/tools/check_contributor_contract.py" --ci
else
  python3 tools/check_contributor_contract.py --ci
fi

