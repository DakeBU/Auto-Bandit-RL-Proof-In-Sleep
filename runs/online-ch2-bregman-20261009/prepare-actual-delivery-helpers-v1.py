from publication_guard_v1 import *
fixed()
old=ROOT/'runs/online-ch2-proximal-20261009'
mapping={
    'publication_guard_v2':'publication_guard_v1',
    'online-ch2-proximal-delivery':'online-ch2-bregman-delivery',
    '3a81dd6ae283fce90b849d928c18094f37b6d3b7':'69aeeeaf58364177a06bbc10329ea328c3c13b3c',
    '29086b6f3a033f6536054f4d9a06ae0e9b2f8a91':'71f2219fa1648094eba8aa17b50e443258f436cb',
    'codex/research-online-ch2-prescient':'codex/research-online-ch2-proximal',
    'PR205':'parent PR208',
    'official-PR208-attachment-v1.json':'official-PR-attachment-v1.json',
    'PR208':'new Bregman PR',
    'publication-status-review-v2.json':'RAW-format-review-v1.json',
    'approved_RAW_EOF_exceptions':'approved_RAW_exceptions',
    'immutable EOF':'immutable LaTex trailing-space',
    'helper1->0':'fiveproofs5->0 (definition separate)',
}
for name in ['collect-actual-delivery-v1.py','final-evidence-delivery-v1.py']:
    s=(old/name).read_text(encoding='utf8')
    for a,b in mapping.items():s=s.replace(a,b)
    s=s.replace(': new blank line at EOF.',': TRAILING_PLACEHOLDER.').replace(': trailing whitespace.',': new blank line at EOF.').replace(': TRAILING_PLACEHOLDER.',': trailing whitespace.')
    if name.startswith('collect'):
        s=s.replace("assert actual['PR']['number']==208", "assert isinstance(actual['PR']['number'],int) and actual['PR']['number']>208")
        s=s.replace('delivered_head=head,PR=208','delivered_head=head,PR=actual[\'PR\'][\'number\']')
    else:
        s=s.replace("['gh','pr','view','208','--json'", "['gh','pr','view',str(packet['PR']),'--json'")
        s=s.replace('Bind actual proximal comparison PR delivery and review evidence','Bind actual Bregman proof PR delivery and review evidence')
    write(RUN/name,s)
print('Actual-delivery collection/evidence helpers prepared create-only; prospective not yet executed.')
