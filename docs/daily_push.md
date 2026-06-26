# Daily GitHub Push

Use this sequence when pushing the repository to
`DakeBU/Auto-Bandit-RL-Proof-In-Sleep`.

## One-Time Remote Setup

```bash
git remote add origin https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep.git
```

If `origin` already exists, update it:

```bash
git remote set-url origin https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep.git
```

## Daily Push

```bash
git status --short
python3 tools/bandit.py check
git add -A
git status --short
git commit -m "Update ABRL harness docs and memory"
git -c credential.helper= push origin main
```

When GitHub asks for credentials:

```text
Username: DakeBU
Password: paste github_pat here
```

Do not put the token into a file, remote URL, commit message, or README.  The
interactive password prompt is the intended daily path.
