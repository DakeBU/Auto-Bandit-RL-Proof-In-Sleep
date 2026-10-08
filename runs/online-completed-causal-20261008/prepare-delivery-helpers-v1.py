from common_body_v2 import *

fixed_integrated()
prior = ROOT / 'runs/online-ae-causal-20261008'
source = (prior / 'prepare-reviewed-commit-v3.py').read_text(encoding='utf8')
source = source.replace('common_accepted_v3', 'common_accepted_v1')
source = source.replace('-v3', '-v1').replace('-v2', '-v1').replace('-v5', '-v1')
source = source.replace('AE causal acceptance, exact F1 repair and current reader evidence',
    'Completed causal acceptance and current shared reader evidence')
source = source.replace('basePR=197', 'basePR=198')
write(RUN / 'prepare-reviewed-commit-v1.py', source)
source = (prior / 'deliver-reviewed-draft-v3.py').read_text(encoding='utf8')
source = source.replace('common_accepted_v3', 'common_accepted_v1')
source = source.replace('-v3', '-v1').replace('-v2', '-v1')
source = source.replace('codex/research-online-c1-core-audit', 'codex/research-online-ae-causal')
source = source.replace('basePR=197', 'basePR=198')
source = source.replace('Bind reviewed AE acceptance source commit and contributor evidence',
    'Bind reviewed completed-information source and contributor evidence')
write(RUN / 'deliver-reviewed-draft-v1.py', source)
write(RUN / 'prospective-delivery-helpers-v1.json', dict(
    authorized_action='Scoped commit/push/reviewable draft PR only; no merge/deploy.',
    actual_delivery_not_yet_performed=True, intended_base=BASE, base_PR=198,
    base_branch='codex/research-online-ae-causal', scoped_existing_helpers_adapted=True,
    mandatory_official_app_attachment_after_creation=True,
    final_native_post_native_review_still_required=True))
