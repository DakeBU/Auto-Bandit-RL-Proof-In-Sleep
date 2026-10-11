"""Read-only generated-site QA, requires actual clean shared gate receipt."""
from pathlib import Path
from html.parser import HTMLParser
from html import unescape
from urllib.parse import urlsplit,unquote
import argparse,json,hashlib,re,subprocess
ROOT=Path(__file__).resolve().parents[2]
def load(p):return json.loads(p.read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(s):return re.sub(r"\s+"," ",s).strip()
class HTML(HTMLParser):
 def __init__(self):super().__init__();self.ids=set();self.links=[];self.text=[]
 def handle_starttag(self,t,attrs):
  a=dict(attrs)
  if "id" in a:self.ids.add(a["id"])
  if t=="a" and "href" in a:self.links.append(a["href"])
 def handle_data(self,s):self.text.append(s)
def parse(p):
 h=HTML();h.feed(p.read_text(encoding="utf8"));return h
class Folds(HTMLParser):
 def __init__(self):super().__init__();self.blocks={};self.current=None;self.depth=0;self.pre=False
 def handle_starttag(self,t,attrs):
  a=dict(attrs)
  if t=="details":
   if self.current is not None:self.depth+=1
   elif "declaration" in a.get("class","").split():self.current={"header":[],"links":[]};self.blocks[a["id"]]=self.current;self.depth=1
  if self.current is not None:
   if t=="pre" and "lean-code" in a.get("class","").split():self.pre=True
   if t=="a" and "href" in a:self.current["links"].append(a["href"])
 def handle_endtag(self,t):
  if self.current is not None:
   if t=="pre":self.pre=False
   if t=="details":
    self.depth-=1
    if not self.depth:self.current=None
 def handle_data(self,s):
  if self.current is not None and self.pre:self.current["header"].append(s)
def local(page,u):
 a=urlsplit(u)
 if a.scheme or a.netloc:return
 p=(page.parent/unquote(a.path)).resolve() if a.path else page
 if p.is_dir():p=p/"index.html"
 assert p.is_file(),u
 if a.fragment and p.suffix==".html":assert unquote(a.fragment) in parse(p).ids,u
p=argparse.ArgumentParser();p.add_argument("--gate",type=Path,required=True);p.add_argument("--gate-sha256",required=True);p.add_argument("--head",required=True);p.add_argument("--before",type=Path,required=True);a=p.parse_args()
assert sha(a.gate)==a.gate_sha256
receipt=load(a.gate);assert receipt["actual_exit"]==0 and receipt["capture_integrity_ok"] is True
assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=str(ROOT)).decode().strip()==a.head
assert subprocess.check_output(["git","status","--porcelain=v1","--untracked-files=all"],cwd=str(ROOT))==b""
post=a.gate.parent/"post-source-inputs.json";assert sha(post)==receipt["post-source-inputs.json_sha256"]
for row in load(post):assert sha(ROOT/row["path"])==row["raw_sha256"],("current source drift",row["path"])
pins={
 "docs/contracts/online-ch2-unbounded-ogd-v1/neutral-frozen-header-v1.txt":"fd0cccb6f5deb86a63466516a49531db7599cb983620072782726e5ecc136efa",
 "docs/contracts/online-ch2-unbounded-ogd-v1/neutral-frozen-definitions-v1.txt":"707df92f3a1660b96427ee14949e10ff92d3095a064ebfcce143c6dd2bdcd2cd",
 "runs/online-ch2-unbounded-ogd-20261011/fresh-core-BODY-review-v1.json":"3c365ded43978cb54bce5e13ed03f93512d3e41698698d4f196aa7900ea868e1",
 "runs/online-ch2-unbounded-ogd-20261011/production-type-value-constants-v1.json":"0dc3e77a28a2918569eba7b66b08e390112f152e9d01f611d48ff42f696a45c7",
 "runs/online-ch2-unbounded-ogd-20261011/fresh-canary-BODY-review-v1.json":"1a55fb1510aa477db32daefc3c211b65637cad627928d5b0f1a519ee5a302113"
}
for path,hsh in pins.items():assert sha(ROOT/path)==hsh,path
body=load(ROOT/"runs/online-ch2-unbounded-ogd-20261011/fresh-core-BODY-review-v1.json")
assert body["verdict"]=="accepted-candidate-core-only" and body["blocking_repairs"]==[]
assert body["frozen_header_sha256"]==pins["docs/contracts/online-ch2-unbounded-ogd-v1/neutral-frozen-header-v1.txt"]
for path,hsh in [("website/content/readings.json.raw","7a250a6cfbe0bc2f3f65e7bcc87a145770e1e17b27195b2e94d1ef765b0e17a4"),("website/content/highlights.json.raw","06fb9e7f745f3785b5b895aeaecd725f068448fc19daaf001723c4badc2d4c32")]:assert sha(a.before/path)==hsh,path

assert "tools/bandit.py" in receipt["argv"] and "check" in receipt["argv"]
for k in ["pre_git","post_git"]:assert receipt[k]["HEAD"]==a.head and receipt[k]["status_porcelain_v1_z_hex"]==""
oldpath=ROOT/"tmp/online-ch2-weighted-identity-site-20261011-v1/books/registry.json"
assert sha(oldpath)=="04e3d32de848b7221b55f0b0cc311dc31a75e512954836f54a5fbc5370878392"
site=ROOT/"tmp/online-ch2-unbounded-ogd-site-20261011-v1";old=load(oldpath);new=load(site/"books/registry.json")
assert new["source_commit"]==a.head and new["lean_verified"] is True
ob={n["id"]:n for n in old["nodes"]};nb={n["id"]:n for n in new["nodes"]};key="declaration:BanditRL.OnlineUnboundedOGD.regret_lower_bound"
assert len(ob)==11100 and len(nb)==11101 and len(nb)==len(new["nodes"])
assert all(nb.get(k)==v for k,v in ob.items()),"old registry object changed"
assert set(nb)-set(ob)=={key};node=nb[key];assert node["status"]=="compiled"
local(site/"index.html",node["url"])
module=site/node["url"].split("#")[0];folds=Folds();folds.feed(module.read_text(encoding="utf8"));block=folds.blocks[node["url"].split("#")[1]]
core=ROOT/"BanditRLProof/OnlineUnboundedOGD.lean";assert sha(core)=="313c8522a40599846d79df32d2a8a42014a3338f814286df7ffe9603554d6b50"
raw=core.read_text(encoding="utf8");header=raw[raw.index("theorem regret_lower_bound "):].split(":= by",1)[0]
assert norm("".join(block["header"]))==norm(header),"rendered raw section-dependent header drift"
line=next(i for i,s in enumerate(raw.splitlines(),1) if s.startswith("theorem regret_lower_bound "))
link="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/"+a.head+"/BanditRLProof/OnlineUnboundedOGD.lean#L"+str(line)
assert link in block["links"]
page=site/"chapters/online-ogd/index.html";h=parse(page);text=" ".join(h.text)
oldread=load(a.before/"website/content/readings.json.raw");cur=load(ROOT/"website/content/readings.json")
oldrow=next(x for x in oldread["readings"] if x["slug"]=="online-ogd");row=next(x for x in cur["readings"] if x["slug"]=="online-ogd")
assert len(oldrow["source_theorems"])==20 and len(row["source_theorems"])==21 and row["source_theorems"][:-1]==oldrow["source_theorems"]
card=row["source_theorems"][-1];assert card["math"] in unescape(page.read_text(encoding="utf8"))
for token in ["NormedAddCommGroup E","InnerProductSpace ℝ E","FiniteDimensional ℝ E","Nontrivial E","horizon-dependent","1-Lipschitz","differentiable"]:assert token in card["plain"] and token in text,token
for token in ["R_T^{\\mathrm{OGD}}(0)","\\frac12","T^{2-\\alpha}","(1-\\alpha)\\phi(\\alpha)"]:assert token in card["math"],token
assert card["url"]=="https://arxiv.org/pdf/1912.13213v10#page=26" and card["url"] in h.links and link in h.links
for u in h.links:local(page,u)
oldhi=load(a.before/"website/content/highlights.json.raw")["highlights"];hi=load(ROOT/"website/content/highlights.json")["highlights"];assert hi[:-1]==oldhi and len(hi)==len(oldhi)+1
lesson=hi[-1];assert lesson["full_name"]==key[len("declaration:"):]
assert lesson["dependencies"]==["BanditRL.OnlineGradientDescentSource.gradient_linear","BanditRL.OnlineUnboundedOSD.currentSubgradient_affine","BanditRL.OnlineUnboundedOSD.switching_loss_regular","BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound"]
assert lesson["proof_idea"] in text
cov=next(x for x in load(ROOT/"docs/contracts/online-book-v1/coverage.json")["chapters"] if x["chapter"]==2)
assert cov["mandatory_count"] is None and cov["accepted"] is False and cov["required_open_forward_containers"]==8 and cov["required_future_mathematical_claims_open_unenumerated"]==6
print(json.dumps({"status":"passed structural QA; personal visual QA separate","candidate_head":a.head,"old_canonical_objects_preserved":11100,"new_production_ids":[key],"source_cards":21,"raw_header_matches_actual_section_source":True,"complete_compiled_TYPE_scope":"Independently bound by core BODY/export/frozen-context receipts; reader explicitly lists ambient hypotheses","chapter_accepted":False,"denominator":None,"source_writes":False},indent=2))
