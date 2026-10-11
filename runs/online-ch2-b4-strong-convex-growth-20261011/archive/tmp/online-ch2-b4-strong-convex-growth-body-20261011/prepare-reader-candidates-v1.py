import collections,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=pathlib.Path(__file__).resolve().parent/'reader-candidates-v1'
OUT.mkdir(exist_ok=False)
NAME='BanditRL.OnlineConvex.stronglyConvex_minimum_growth'
plain=('Let E be a real normed space and f:E to EReal be SourceProper: f never equals bottom and has a finite value somewhere. '
       'Let V be convex and contained in effectiveDomain f, so all feasible values are finite, and let lambda>=0. '
       'Assume the strong-convex segment inequality with coefficient lambda/2 for every feasible pair and every real weight 0<a<1. '
       'Supply p in V attaining the minimum over V. Then every q in V satisfies f(p)+(lambda/2)||q-p||^2<=f(q), read through toReal only at these finite endpoints.')
boundary=('This is a locally compiled conditional B4 dependency. It does not prove existence or uniqueness of a minimum, '
          'an actual cumulative FTRL/BTRL minimizer, or either corrected full performance bound. '
          'Chapter 2 remains partial with seven required forward containers and six future claims open; B1-B7, full B4 and corrected7.47/15.31 remain open. Unmerged and unpublished.')
proof=('Write c=(lambda/2)||q-p||^2 and g=f(q)-f(p)>=0. If g<c, then c>0 and a=(g+c)/(2c) lies strictly between0 and1. '
       'Convex feasibility, minimality at p and strong convexity give f(p)<=a f(p)+(1-a)f(q)-c a(1-a). '
       'Thus (1-a)(g-ca)>=0. But ca=(g+c)/2>g and1-a>0, a contradiction. '
       'When lambda=0 or p=q, no violating gap can enter this contradiction branch. '
       'The Lean proof composes the extended-real order inequalities before converting their finite endpoints; it never assumes a finite value by silently totalizing infinity.')
math=(r'\begin{gathered}f(p)+\frac{\lambda}{2}\lVert q-p\rVert^2\le f(q),\quad p\in\operatorname{argmin}_{x\in V}f(x),\quad q\in V.'
      r'\\c=\frac{\lambda}{2}\lVert q-p\rVert^2,\quad g=f(q)-f(p)\ge0.'
      r'\\g<c\Longrightarrow a=\frac{g+c}{2c}\in(0,1),\quad 0\le(1-a)(g-ca)<0.\end{gathered}')
highlight=dict(full_name=NAME,title='Quadratic growth at a supplied feasible minimum',chapter='online-ogd',featured=False,
    teaching_order=345,source_match='closest-source',plain=plain,math=math,
    intuition='Strong convexity prevents a point far from an attained minimum from having almost the same objective value.',
    why='A genuine extended-real conditional growth component for the still-open corrected B4 FTRL/BTRL routes.',
    position='Derived consequence of Definition4.1 (printed34/PDF46), with properness from Definition2.18 (printed16/PDF28). Mapped here as a Chapter2 B4 dependency; no Chapter4 main closure or full7.47/15.31 claim.',
    proof_idea=proof,
    lean_notes=('The exact public header preserves SourceProper, literal V subset effectiveDomain, lambda>=0 and lambda/2. '
        'hp/hmin/hq are conditional target data, not proof ingredients or existence producers. '
        'The real normed ambient explicitly generalizes the source finite-dimensional setting; no completeness, closedness, differentiability or finite-dimensional hypothesis is added. '
        'The source support topology is separate from this direct segment implementation. Actual compiled VALUE occurrences include EReal.coe_toReal, EReal.toReal_le_toReal and norm_sub_rev; occurrence is not logical necessity or a full transitive dependency graph. '+boundary),
    dependencies=['BanditRL.OnlineConvex.SourceProper','BanditRL.OnlineConvex.effectiveDomain'])
card=dict(label='Derived B4 dependency: quadratic growth at a supplied minimum',pages='Definition4.1 printed34 / PDF46; Definition2.18 printed16 / PDF28',pdf_page=46,
    url='https://arxiv.org/pdf/1912.13213v10#page=46',math=math,plain=plain,
    fallback='A supplied feasible minimum of a strongly convex extended-real objective has quadratic growth on its finite convex domain.',
    relationship=('This is a derived conditional consequence of the pinned definition, with an explicit normed-space generalization; it is not a newly attributed numbered theorem or the complete Chapter4 main result. '
        'The literal source-support route and actual implementation proof dependencies stay separate. '+proof+' '+boundary),
    contract=dict(model='One proper extended-real objective on a convex finite feasible set; no algorithmic run or selected cumulative objective is asserted.',
        assumptions=plain,parameters='lambda>=0; a supplied attained minimum p and any feasible comparator q. The coefficient is exactly lambda/2.',
        regret='No regret bound in this leaf. Full corrected FTRL7.47/BTRL15.31 producers and bounds remain open.',
        guarantee='The displayed quadratic minimum-growth inequality, including lambda=0 and coincident points. '+boundary),
    local_status=dict(status='compiled',label='Locally compiled conditional growth dependency',boundary=boundary))
inputs=[]
for filename,key in [('highlights.json','highlights'),('readings.json','readings'),('chapters.json','chapters')]:
    source=ROOT/'website/content'/filename; old=json.loads(source.read_bytes()); new=json.loads(source.read_bytes())
    if filename=='highlights.json':
        assert all(x.get('full_name')!=NAME for x in old[key]);new[key].append(highlight)
        counter=lambda rows:collections.Counter(json.dumps(x,sort_keys=True,ensure_ascii=False) for x in rows)
        assert counter(new[key])-counter(old[key])==counter([highlight]) and not counter(old[key])-counter(new[key])
    elif filename=='readings.json':
        target=next(x for x in new[key] if x['slug']=='online-ogd');target['source_theorems'].append(card);target['teaching_route'].append(NAME)
    else:
        target=next(x for x in new[key] if x['slug']=='online-ogd');target['module_globs'].append('BanditRLProof/OnlineStrongConvexMinimum.lean')
    out=OUT/filename
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(new,f,ensure_ascii=False,indent=2);f.write('\n')
    inputs.append(dict(source=source.relative_to(ROOT).as_posix(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        candidate=out.relative_to(ROOT).as_posix(),candidate_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
manifest=dict(status='READER_CONTENT_CANDIDATES_ONLY',author='/root',inputs=inputs,production_changed=False,
    core_declaration=NAME,proof_accepted=False,maintenance_accepted=False,Goal='ACTIVE',
    scope='One conditional B4 dependency card/lesson/Book ownership; all inherited object multiplicities retained, no chapter acceptance or source theorem number invented.')
with (OUT/'manifest-v1.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(manifest,f,indent=2);f.write('\n')
print(json.dumps(manifest))
