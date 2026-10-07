from common_integrated_v1 import *
fixed_integrated()
p=Path('website/content/readings.json');data=load(p);row=next(x for x in data['readings'] if x['slug']==ROUTE);card=row['source_theorems'][9]
old=card['math'];needle=r'\\[\forall';assert old.count(needle)==1
write(RUN/'reader-math-before-TeX-repair-v1.json',card)
card['math']=old.replace(needle,r'\\{}[\forall',1)
p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'reader-TeX-repair-v2.json',dict(reason='TeX optional row-spacing parser can consume a leading bracket immediately after aligned row break. Same hazard was actually found in previous package pixel review; current formula inspection found one such pattern before site rendering.',repair='Insert empty group between row break and displayed convergence-premise bracket, preserving exactly the same mathematical glyphs/quantifiers. Original formula card retained; no claimed failed current site gate.',source_or_terminal_or_public_canary_changed=False,old_formula_sha256=hashlib.sha256(old.encode()).hexdigest(),new_formula_sha256=hashlib.sha256(card['math'].encode()).hexdigest(),R1_to_R8_unchanged=True))
fixed_integrated();print('One TeX rowbreak separator repaired before actual current render; no mathematical changes.')
