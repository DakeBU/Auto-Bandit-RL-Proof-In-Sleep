from publication_guard_v1 import *
fixed()
registry = load(SITE / 'books/registry.json')
n = next(n for n in registry['nodes'] if n['id'] == 'declaration:BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained')
node_id = n['url'].split('#')[1] + '-teaching'
for label, p in [('generated', SITE / 'chapters/online-ogd/index.html'), ('actual_DOM', RUN / 'formula-render-v1-dom.html')]:
    s = p.read_text(encoding='utf8')
    i = s.index('id="' + node_id + '"')
    print(label, s[i:i+5500])
