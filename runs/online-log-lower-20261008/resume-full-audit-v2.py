from common_v1 import *
fixed()
assert load(RUN/'all-axioms-v1-exit.json')['exit_code']==0
assert load(RUN/'all-exact-types-v3-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-full-body-v1.lean.raw').read_bytes()
assert CANARY.read_bytes()==(RUN/'snapshots/canaries-body-v3.lean.raw').read_bytes()
actual=load(RUN/'actual-public-canary-headers-v1.json')
TEST='GuessingLogLowerProbe.'
pubdefs=re.findall(r'(?m)^(?:noncomputable )?def (\w+)\b',PUBLIC.read_text(encoding='utf-8'))
testdefs=re.findall(r'(?m)^(?:noncomputable )?def (\w+)\b',CANARY.read_text(encoding='utf-8'))
names=[x['name'] for x in actual]+[PRE+n for n in pubdefs]+[TEST+n for n in testdefs]
log=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8')
assert 'sorryAx' not in log
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matched)==len(names)==76
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write(RUN/'audit-resume-v2.json',dict(
    previous_audit_failed_at='Neutral-vs-actual rfl type binding; exact raw failure retained',
    public_or_canary_changed=False,axiom_gate_still_applicable=True,
    exact_bindings_gate='all-exact-types-v3',
    nominal_or_recursive_bridges='Actual list induction, funext, and propext of both distribution fields; no axioms or target weakening',
    source_or_frozen_target_changed=False))
original=(RUN/'audit-full-bodies-v1.py').read_text(encoding='utf-8')
suffix=original[original.index("template=Path("):]
suffix=suffix.replace("    exact_closed_proposition_identities=64,exact_definition_identities=12,",
    "    exact_closed_proposition_identities=64,exact_definition_identities=12,\n    exact_binding_method='64 actual Prop equalities/12 function equalities, with explicit recursive/nominal equality bridges where rfl is insufficient',\n    exact_bindings_gate='all-exact-types-v3',")
exec(compile(suffix,'audit-full-bodies-v1.py:resume','exec'))
