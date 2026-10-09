from lower_common_v1 import *

reviewed(); headers(3)
for name in ['statement-fence','safe-verify','frontier-refresh','frontier-shadow']:
    capture('nonsmooth-'+name+'-help-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',name,'--help')
source=ROOT/'runs/online-c1-chapter-audit-20261009/export-general-init-readiness-v1.lean'
s=source.read_text(encoding='utf8')
start=s.index('def moduleName')
common=s[start:]
common=common.replace('Lean.importModules #[{ module := `BanditRLProof }, { module := `BanditRLProof.OnlineFTLInitializationRegret }]',
    'Lean.importModules #[{ module := `BanditRLProof.OnlineNonsmoothExamples }, { module := `Tests.OnlineNonsmoothExamplesCanary }]')
assert 'OnlineFTLInitializationRegret' not in common
old='Fifty unchanged reused Chapter1 public proof targets, four exact actual general-initial FTL bodies and selected support definitions. Compiled current readiness only, not source/chapter acceptance. Selected coalesced direct TYPE_VALUE constant presence, not full transitive proof graph or new theorem count.'
assert old in common
common=common.replace(old,'Three exact new nonsmooth production proofs, five complementary canary proofs and actual shared parents. Selected direct TYPE_VALUE constant presence, not occurrence counts, full transitive graph, shared registry, new source theorem count or chapter acceptance.')
names=[t['declaration'] for t in reviewed()['targets']]+[t['declaration'] for t in load(CONTRACT/'nonsmooth-canary-contracts-v2.json')['targets']]
names+=['BanditRL.OnlineConvex.'+n for n in ['affine_convex','convexExtended_coe_iff','example_2_27','theorem_2_22','sourceDifferentiableAt_regular']]
text='''import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineNonsmoothExamplesCanary
import Lean
import Lean.Util.FoldConsts
open Lean

def targets : Array Name := #[
'''+',\n'.join('`'+n for n in names)+']\n\n'+common
write(RUN/'export-nonsmooth-dependencies-v1.lean',text)
write(RUN/'nonsmooth-graph-required-value-pairs-v1.json',dict(
    scope='direct compiled proof VALUE presence, not import implication or source acceptance',
    pairs=[
      [names[0],'convexOn_univ_norm'],[names[0],'not_differentiableAt_abs_zero'],
      *[[names[1],n] for n in names[8:]], [names[2],names[1]],
      [names[3],names[0]],[names[4],names[2]],[names[5],names[2]],[names[6],names[1]],[names[7],names[2]]],
    exporter_source_sha256=sha(source),new_exporter_sha256=sha(RUN/'export-nonsmooth-dependencies-v1.lean'),
    chapter_complete=False,whole_Goal_status='ACTIVE'))
reviewed(); headers(3)
print('Actual help captured; selected compiled graph exporter and required VALUE pairs frozen before execution.')
