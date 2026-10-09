from common_v1 import *
import base64
fixed()
assert load(RUN/'trial-variable-readiness-v1.json')['actual_exit']==1
assert (RUN/'20_architect-nonsmooth-route-v1.md').is_file()
commands=[
 ('trial-variable-readiness-v2',['trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--notes','Existing exact variable OGD current readiness only: focused9107jobs plus whole-type/value kernel actual0; seven inspected standard axiom records. No new production math. Native omitted obligation counters default0 are unmeasured schema defaults, NOT chapter coverage; actual chapter count remains null.','--run-id',RUN.name,'--progress-class','retrieval-reuse','--verifier-evidence','runs/online-ch2-chapter-audit-20261009/variable-readiness-inspected-v1.json']),
 ('trial-source-enumeration-repair-v2',['trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','rejected','--notes','Distinct source enumeration v1 rejected only for E1-E8 draft precision; exact report retained. Versions2/3 repair without old proof mutation, new finite statement/source repair review pending. Native default0 counters unmeasured, source proof count null.','--run-id',RUN.name,'--progress-class','diagnostic','--verifier-evidence','runs/online-ch2-chapter-audit-20261009/source-enumeration-review-v1.json']),
 ('trial-nonsmooth-type-retrieval-v2',['trial-log','--task',TASK,'--role','middle','--kind','plan','--status','executed','--notes','Scoped actual reference-index/cards/search/local-decls plus exact proposition/API probe actual0; no theorem BODY. Type elaboration not proof completion. Two declaration-name helper failures retained and fixed by exact current registry; native trialv1 invalid kind1 retained, fixed from actual CLI validation. Native default0 obligation counters unmeasured, chapter totalsnull.','--run-id',RUN.name,'--progress-class','retrieval-reuse','--verifier-evidence','runs/online-ch2-chapter-audit-20261009/nonsmooth-type-api-probe-v1.json'])]
for label,args in commands:
 tick=time.monotonic();p=subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'native-scoped-v1.py')]+args,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(RUN/(label+'.json'),dict(command=[sys.executable,'-B','-X','utf8','OWN native-scoped-v1.py']+args,actual_exit=p.returncode,seconds=time.monotonic()-tick,
  stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 assert p.returncode==0,label
write(RUN/'memory-digest-preproof-v2.md','''# OWN preproof memory digest

Whole-book Goal ACTIVE. Chapter1 exact scoped final delivery accepted097359ac on draft PR203, not main/live. New C2 branch base097359ac, canonical main6847 unchanged. All16source original pages reread. Existing variable OGD exact header/full BODY prior review reuse plus current focused9107jobs and seven-standard-axiom kernel pass: no new mathematical proof credited.

Source draftv1 independently rejected for precision; version3 repairs all additional branches/current exact declaration join and proper forward/historical classification. Source/proof totals remain null;65overlapping containers and534retrieved declarations are not independent theorem/coverage counts. New finite types for two nonsmooth families (three terminals) have complete separate blind reconstruction and actual type/API probe0; distinct source/repair decision pending, no production BODY yet. Existing full hinge supports and singleton differentiability producers reused, zero effective normal constant1 explicit. Source forward prescient negative Bregman movement/Chapter5 lower bounds and future statistical/adaptive/parameter-free results remain required/open whole-book dependencies. Chapter7FTRL pointer found in HistoryPDF35, not a new mandatoryC2 theorem.

Failures preserved: defaultPython38 lacksPDF renderer (bundled runtime repaired); two actual-name join helper lookup failures (qualified actual registry repaired); native trialv1 invalid kind actual1 (actual role/kind/status validation inspected and version2 actual0 records). Native omitted obligation counters0 are unmeasured schema defaults, not proof-total or coverage evidence. No proof attempt failure yet and no weakened terminal. OWN trials/index/memory/lifecycle only; globalSGB/frontier untouched. All Chapter2/whole-book acceptance gates and delivery still pending.
''')
fixed();print('All three actual scoped native trial records succeeded; invalid-schema v1 retained, no production theorem BODY yet.')
