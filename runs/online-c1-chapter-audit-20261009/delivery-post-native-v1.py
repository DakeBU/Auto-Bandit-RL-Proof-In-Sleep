from common_reader_v8 import *
import base64
fixed()
capture=load(RUN/'formula-render-v3.json')
for r in capture['images']:assert sha(r['path'])==r['sha256']
assert capture['generated_site_files_unmodified']
write(RUN/'root-reader-pixel-review-v3.json',dict(
 actor='/root',personally_viewed_current_original_files=capture['images'],image_count=10,
 source_commit=capture['source_commit'],actual_tool='view_image detail original; tool display resized tall images',
 observations='All ten current original files personally viewed before this receipt. Current status text points to the versioned chapter-gate ledger without asserting acceptance. Source correction is explicit. Formulas and complete wrapped public types are readable; positive horizon, unit prefix/all-time hypotheses, TRUE-best versus fixed-comparator metrics, and upper versus ordinary semantics remain explicit. Exact Lean is initially folded. No visible clipping or horizontal overflow in these desktop captures.',
 scope='1440px desktop only; no mobile, physical-device, or all-viewports claim',
 current_DOM_report_sha256=sha(RUN/'formula-render-v3-browser.json'),capture_receipt_sha256=sha(RUN/'formula-render-v3.json'),
 distinct_post_native_pending=True,chapter_complete=False,goal_complete=False))
body='''Chapter 1 permits any legal initial FTL prediction, while the existing performance endpoints covered initialization at one half. This package proves the exact first-loss correction for the same causal predictor, the legal-initial `1 + 4 sum_{s=2}^T 1/s` true-best regret bound, upper no-regret, and convergence of true-best average regret to zero. It preserves existing half-initial statements and adds 27 public canaries covering initialization, causality, IID benchmarks and the ordinary-limit obstruction.

The Chapter 1 audit covers 17 main-text source objects against Orabona arXiv:1912.13213v10 (SHA-256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`). The source's ordinary finite comparator-limit wording, its counterexample, and a separately reviewed upper-semantics reconciliation remain explicit. Expected fixed-comparator minima stay outside expectation. Derived constants and explicit stochastic information models are identified. The 54 generic contracts and 27 canaries are not a proof denominator or coverage percentage.

Actual combined library root (9105 jobs), `Tests` (9270 jobs), and full `python tools/bandit.py check` passed, including 472 Python tests with 7 skips and the proof exporter. Frozen statement hashes, actual public theorem values, standard-only axiom audits, native statement fences, direct VALUE dependencies and the own-task shadow check have separate evidence. These Lean inputs and pins remain unchanged. The clean local status site built from `14567d019c31f8f307ac5ab765144ae7d71f1ea1`, its site/registry checks and both nonempty contributor bases passed. The shared registry preserves all 10977 prior records and adds exactly four public theorem nodes. Current browser capture and wrapper both exited 0; the formalizer inspected all ten current images. Old links and teaching routes remain.

The distinct source reviewer accepted the source integration with explicit deltas (all 17 objects and seven semantic slots; no blocking repairs), and the own-task native source-review lifecycle entry and shadow check were executed. This does not yet constitute Chapter 1 acceptance: the separate post-native/status-site and published-delivery review is pending. Historical rejected statements, corrections and failed commands remain versioned. The earlier capture wrapper failure and exact restoration of historical evidence are retained. Cumulative diff checking exits 2 on fourteen SHA-bound RAW evidence exceptions (twelve logs and two frozen decoder reports); the scoped code/Test/reader/contract check exits 0. Thirteen exceptions were accepted at source FINAL; the additional raw successful-push log awaits post-native adjudication. No unexcluded clean cumulative diff is claimed.

Draft stacked on PR #202, exact base `a03f304522ed30ee34d43b38bd67deffbbf3b08f`, branch `codex/research-online-ftl-obstruction`. That dependency remains open and unmerged. No chapter acceptance, whole-book completion, merge, deployment or main/live update is claimed by this description. Chapters 2-16 and required appendix dependencies remain in the active Goal.

Evidence: `runs/online-c1-chapter-audit-20261009/`; frozen contracts/source maps: `docs/contracts/online-c1-chapter-audit-v1/`. Source FINAL: `FINAL-review-v1.md`, `FINAL-receipt-v1.json`; status site: `site-build-v4-exit.json`, `registry-v4.json`, `formula-render-v3.json`; native: `post-FINAL-shadow-gate-v1.json`. Distinct reviewer actors are model agents, not human or external reviewers.
'''
write(RUN/'PR-BODY-post-native-v2.md',body)
def encoded(label,args):
 start=time.monotonic();p=subprocess.run(args,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(RUN/(label+'.json'),dict(command=args,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 assert p.returncode==0,(label,p.returncode)
 return p.stdout
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert head=='14567d019c31f8f307ac5ab765144ae7d71f1ea1'
encoded('delivery-post-native-push-v1',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
encoded('delivery-post-native-description-v2',['gh','pr','edit','203','--body-file',str(RUN/'PR-BODY-post-native-v2.md')])
pr=json.loads(encoded('delivery-post-native-PR203-API-v1',['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/203']))
assert pr['state']=='open' and pr['draft'] and pr['head']['sha']==head and pr['base']['ref']=='codex/research-online-ftl-obstruction' and pr['base']['sha']==BASE
assert pr['body'].strip()==body.strip()
parent=json.loads(encoded('delivery-post-native-PR202-API-v1',['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/202']))
assert parent['state']=='open' and not parent['merged'] and parent['head']['sha']==BASE
write(RUN/'delivery-post-native-state-v1.json',dict(PR_url=pr['html_url'],actual_remote_head=head,local_head=head,draft=pr['draft'],state=pr['state'],merged=pr['merged'],stacked_base=BASE,stacked_base_branch=pr['base']['ref'],parent_PR202_open_unmerged=True,body_sha256=sha(RUN/'PR-BODY-post-native-v2.md'),actual_published_body_matches=True,official_app_attachment_previously_succeeded=True,attachment_not_inferred_from_API=True,chapter_complete=False,goal_complete=False,main_live_updated=False))
print('Current ten-pixel receipt written; actual push, description update and exact PR203 head/body verified.',flush=True)
