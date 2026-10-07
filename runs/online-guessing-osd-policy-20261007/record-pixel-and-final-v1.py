"""Record the seven actual images ROOT has just inspected, then freeze current FINAL inputs."""
from common_v1 import *
headers();reg=load(RUN/'registry-v1.json');render=load(RUN/'formula-render-v1.json');browser=load(RUN/'browser-v1-binding.json')
assert reg['source_commit']==render['site_source_commit'] and reg['new_registry_nodes']==4
p=RUN/'reader-first-viewport-v1.png';write(p,Path(browser['snapshot']).read_bytes());assert sha(p)==browser['snapshot_sha256']
images=[dict(path=p.as_posix(),sha256=sha(p),scope='actual first viewport only')]
for x in render['images']:assert sha(x['path'])==x['sha256'];images.append(dict(**x,scope='actual expanded source-card screenshot'))
assert len(images)==7
write(RUN/'pixel-review-v1.json',dict(status='passed actual ROOT image inspection',actor='/root',source_commit=reg['source_commit'],generated_page_sha256=render['generated_page_sha256'],images=images,observations=['Actually viewed first viewport and all six complete expanded source cards.','Whole translated support cases show both closed endpoints and actual projection; all old mathematical formulas remain readable.','New finite formula uses same policy trajectory, zero-based range and all feasible comparators; its constant-one refinement is explicitly derived.','New eventual formula is a horizon-family one-sided upper statement; actual fixed parameters and played legality remain visible.','Current versus historical canonical evidence, source/Lean delta and remaining Chapter1/2/appendix/whole Goal obligations remain visible.','No MathJax error placeholder or source-card horizontal clipping in the actual seven images.'],limits=['Local headless desktop first viewport and six expanded cards only.','No full-page/mobile/physical-device/live-publication claim.'],generated_site_unmodified=True))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'prepare-final-review-v1.py')],check=True)
headers();print('Actual ROOT-viewed images recorded and FINAL frozen; distinct source review pending.')
