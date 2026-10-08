from common_v1 import *

fixed()
for label in ['actual-draft-types-and-API-v1', 'actual-neutral-types-v1']:
    assert load(RUN / (label + '-exit.json'))['exit_code'] == 0
public = (RUN / 'draft-types-and-API-v1.lean').read_text(encoding='utf8')
neutral = (CONTRACT / 'neutral-context-v1.lean').read_text(encoding='utf8')
assert neutral.startswith('import Mathlib\n')
identities = ['example : DraftExpected.Q' + str(i).zfill(3) + ' = NeutralExpected.Q' + str(i).zfill(3) + ' := rfl' for i in range(1,9)]
identities += ['example : @BanditRL.OnlineLearning.' + name + ' = @NeutralExpected.C' + str(i) + ' := rfl' for i, name in
    enumerate(['expectedFixedMinimum', 'expectedFixedRegret', 'empiricalMean', 'meanPredict'])]
scratch = 'import Mathlib\n' + public + '\n' + neutral[len('import Mathlib\n'):] + '\n' + '\n'.join(identities) + '\n'
write(RUN / 'draft-neutral-identities-v1.lean', scratch)
gate('actual-draft-neutral-identities-v1', 'lake', 'env', 'lean', RUN / 'draft-neutral-identities-v1.lean')
write(RUN / 'draft-type-verification-v1.json', dict(status='passed', eight_closed_Prop_type_identities=True,
    four_whole_definition_identities=True, actual_API_checks=True,
    targets_sha256=sha(CONTRACT / 'targets-v1.json'), public_context_sha256=sha(CONTRACT / 'public-context-v1.lean'),
    neutral_context_sha256=sha(CONTRACT / 'neutral-context-v1.lean'), new_public_proof_bodies_compiled=False,
    source_fidelity_accepted=False, chapter_complete=False, goal_complete=False))
write(RUN / 'retrieval-packet-v1.md', '''# Actual retrieval before stabilization/proving

Source card: local source-qualified ORABONA-V10-C1-IID-BENCHMARK, printed1–2/PDF13–14. Scenario: SCN-ONLINE-GUESSING-IID-AE-STRICT-HISTORY (task-local canonical contract), same squared loss/unit interval and finite strict-history information order. Actual native reference-index run writes only own RUN/native-reference-index, existing globalSGB/frontier unchanged. Mathlib cards MLIB-MEASURE-INTEGRAL, MLIB-PROBABILITY-INDEPENDENCE, MLIB-PROBABILITY-VARIANCE, MLIB-FINSET-SUMS, MLIB-ORDER-ALGEBRA read, plus mathlib-candidate rules. Paper/frontier and proof-weapon cards read; none is a proof certificate or needed inspiration. No LML/Optlib/external dependency needed; no dependency/toolchain upgrade.

Actual native search-memory/list-lean-decls --statement searches expected_square_decomposition, independent_prediction_square, history_policy_independent and expectedFixedMinimum; exact expectedFixedMinimum returned no existing theorem before new production module. Current lake env lean #checks bind actual local types/bodies from the pinned shared toolchain. expected_square_decomposition and independent_prediction_square are existing actual L2 square identities, not assumed regret statements. source_mean_optimal and iid_meanPredict_excess actually require pointwise observation bounds; the new targets keep a.s. support, so those old endpoints cannot simply be invoked by strengthening the frozen contract. No duplicate square-decomposition theory is written.

Current history_policy_independent derives independence by disjoint finite target tuples and measurable composition; no scalar prediction independence assumption is supplied to the genuine history producer. Actual meanPredict_independent uses independent strict-past sum; meanPredict_measurable/mem retain first1/2 and exact strict-past mean. Frozen generic cumulative consumer I004 has TWO actual planned consumers I005/I006; it is shared rather than separate duplicated cumulative proof trees, and cannot close the source alone.

Imported Mathlib API types actually checked: integral_finset_sum requires each actual square-loss Integrable; MemLp.integrable_sq supplies it after a.s. bounded MemLp_of_bounded, not source-integral totalization. integral_nonneg_of_ae/integral_mono_ae prove distribution mean in[0,1] using a.s. bounds; ae_all_iff combines countably many a.s. interval events for actual meanPredict. IsLeast.csInf_eq applies only after constructed image membership/lower bounds. normalized_excess actual header requires positive natural horizon. These generic APIs already exist, so no new general Mathlib candidate is introduced; new minimum/finite IID benchmark adapters are project/source-local and bounded.

Eight closed draft/neutral Props and four full definition identities actually compile; that is statement/context evidence, not theorem-body/source acceptance. Original type/source SHA remains frozen. First finite leaf I001: derive observation L2, finite-sum square integrability; rewrite each expectation with actual expected_square_decomposition and IdentDistrib integral/variance equality; sum constant real terms with Finset.sum. Next actual minimizer then sInf before causal producers. Default one lower route; failures/repairs recorded, not silent terminal weakening.

Canary retrieval: pinned Mathlib Probability.Independence.InfinitePi exposes iIndepFun_infinitePi and measurePreserving_eval_infinitePi (local source search only at this stage), giving a true infinite product Bernoulli-coordinate fixture candidate. Actual nondegenerate IID fixture proof/positive variance and expected fixed minimum versus expected hindsight minimum separation must compile before acceptance; no simulation substitutes for that proof. Randomized/abstract-filtration source-wide scope and source asymptotic-success equivalence remain mandatory separate work.
''')
fixed()
print('Eight draft Prop/four whole-context identities actually compiled; body/source acceptance still pending.')
