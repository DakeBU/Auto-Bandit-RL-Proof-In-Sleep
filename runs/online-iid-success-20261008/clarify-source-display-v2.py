from common_integrated_v1 import *
fixed_integrated()
p=Path('website/content/readings.json')
write(RUN/'snapshots'/'own-success-card-before-source-display-v2.raw',p.read_bytes())
d=load(p);row=next(x for x in d['readings'] if x['slug']==ROUTE)
card=row['source_theorems'][-1]
assert card['label']=='Stochastic success and the actual sample-mean learner'
before=card['math']
needle=r'0\le\mathcal E_T(x)'
assert before.count(needle)==1
source_display=(r'R_T(x,y)&=\sum_{t<T}(x_t-y_t)^2-\min_{u\in[0,1]}\sum_{t<T}(u-y_t)^2'
    r'\\&\le4+4\ln T\quad(T\ge1,\ y_i\in[0,1]),\\')
card['math']=before.replace(needle,source_display+needle)
card['relationship']+=' The displayed R_T(x,y) is the original pathwise Theorem1.3; the displayed expected excess upper and success are its derived applications.'
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
proposal=load(RUN/'reader-proposal-v1.json')
proposal['card']=card
write(RUN/'reader-proposal-v2.json',proposal)
write(RUN/'reader-source-display-clarification-v2.json',dict(
    required_reader_id='R1',change='Add the actual original pathwise Theorem1.3 display adjacent to its derived expected success, explicitly separate the two',
    old_source_cards_exactly_retained=13,math_proof_or_statement_change=False,
    before_snapshot=sha(RUN/'snapshots'/'own-success-card-before-source-display-v2.raw'),
    current_reader_sha256=sha(p),FINAL_review_pending=True))
fixed_integrated()
