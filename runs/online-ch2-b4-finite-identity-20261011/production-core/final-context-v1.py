from pathlib import Path
import json,hashlib,datetime,subprocess
root=Path('E:/ABRL/worktrees/research-online-book'); out=root/'tmp/online-ch2-b4-finite-identity-core-20261011'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,s):
 with (out/n).open('xb') as f:f.write(s.encode('utf-8'))
rows=json.loads((root/'tmp/online-ch2-b4-finite-identity-preproof-20261011/capture-v3/source-RAW-before.json').read_text()); current=[]
for r in rows:
 b=(root/r['path']).read_bytes();actual=sha(b);assert actual==r['sha256'],r['path'];current.append(dict(path=r['path'],sha256=actual,bytes=len(b)))
core=(root/'BanditRLProof/OnlineCumulativePotential.lean').read_bytes();frozen=(root/'docs/contracts/online-ch2-b4-finite-identity-v1/neutral-frozen-header-v1.txt').read_bytes()
erased=core.split(b' := by\n',1)[0]+b'\n\nend BanditRL.OnlineCumulativePotential\n';assert erased==frozen
put('context-after-core-v1.json',json.dumps(dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),HEAD=subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip(),git_status=subprocess.check_output(['git','status','--short'],cwd=str(root)).decode().strip(),all_preproof_rows_unchanged=True,rows=current,core_sha256=sha(core),header_erasure_sha256=sha(erased),whole_header_context_exact=True),indent=2)+'\n')
put('reader-proof-outline-v1.md','''The finite-real identity is established for an arbitrary spliced trajectory y, arbitrary losses and regularizers, and positive finite T.

1. Inclusive cumulative potentials satisfy G_(n+1)(v) = G_n(v) + psi_(n+1)(v) - psi_n(v) + loss_(n+1)(v). This is Finset.sum_range_succ and real algebra.
2. Prove the displayed identity for every prefix n+1 while keeping y fixed. The one-round base case is the direct difference of G_0 values. At the successor, split the final loss difference, the final within-round potential difference, and the final regularizer drift. Substituting the cumulative-potential recurrence cancels the interior terms; the induction hypothesis leaves exactly the new endpoint gap.
3. Instantiate n=T-1. Positivity gives (T-1)+1=T; the literal endpoint splice gives y(T)=z. No minimizer, convexity, or algorithm premise is used.

Actual authored mathematical parents: Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_add_cancel, ordinary real ring/linear arithmetic and equality simplification. The compiled constant-occurrence export supplies the full elaborator-level TYPE/VALUE inventory; it is neither a minimal necessity claim nor a transitive graph.

Boundary: this proves only the frozen finite-real algebra identity locally. EReal finiteness adaptation, attainment, optimizer/trajectory producers, sharp Young endpoints, complete B4 parents, all seven containers and six future claims, chapter/Goal closure and integration remain open. A distinct BODY review is still required.
''')
print('context and outline saved')