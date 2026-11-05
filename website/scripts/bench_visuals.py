"""Small, accessible SVG explanations and progressive disclosure for Bench."""
import html
import re


def picture(kind):
    shapes = {
        'knowledge': '<path d="M28 30Q58 18 90 30V106Q58 94 28 106Z M90 30Q122 18 152 30V106Q122 94 90 106Z M90 30V106"/><path d="M40 46H74M40 60H74M106 46H140M106 60H140"/>',
        'reasoning': '<path d="M30 35H72L100 70H148M72 35L100 105H148"/><circle cx="30" cy="35" r="9"/><circle cx="100" cy="70" r="9"/><circle cx="100" cy="105" r="9"/><path d="M135 32L143 40L157 22"/>',
        'agentic': '<rect x="25" y="24" width="130" height="76" rx="8"/><path d="M40 45L51 54L40 63M61 63H83M60 118H120M90 100V118"/><path d="M115 53A20 20 0 1 1 112 80M112 80L110 67M112 80L125 78"/>',
        'graph': '<path d="M40 70L90 28L140 70L90 112Z M40 70H140M90 28V112"/><circle cx="40" cy="70" r="10"/><circle cx="90" cy="28" r="10"/><circle cx="140" cy="70" r="10"/><circle cx="90" cy="112" r="10"/>',
        'hypergraph': '<ellipse cx="72" cy="65" rx="45" ry="31" stroke-dasharray="5 4"/><ellipse cx="112" cy="80" rx="45" ry="31" stroke-dasharray="5 4"/><circle cx="51" cy="62" r="7"/><circle cx="90" cy="70" r="7"/><circle cx="132" cy="88" r="7"/>'}
    return '<svg class="bench-picture" viewBox="0 0 180 140" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round">'+shapes[kind]+'</svg>'


def landing():
    cards = ''.join('<a class="bench-path" href="'+route+'/index.html">'+picture(icon)+'<span class="eyebrow">'+label+'</span><h2>'+title+'</h2><p>'+desc+'</p><span>Explore →</span></a>' for icon,label,title,desc,route in [
        ('knowledge','01 · Knowledge','Know the field','Definitions, assumptions and guarantees.','non-lean'),
        ('reasoning','02 · Reasoning','Explain the mathematics','Proofs, counterexamples and missing steps.','non-lean'),
        ('agentic','03 · Agentic Lean','Explore. Prove. Verify.','Tool-using tasks with exact formal targets.','protocol')])
    graphs = ''.join('<a class="bench-graph-door" href="../'+path+'/index.html">'+picture(icon)+'<span><strong>'+title+'</strong><small>'+desc+'</small></span><b aria-hidden="true">↗</b></a>' for icon,title,desc,path in [
        ('graph','Lean Graph','Find the exact declaration and its library context.','lean-graph'),
        ('hypergraph','Functor Hypergraph','Explore conceptual connections across settings.','functor-hypergraph')])
    return ('<section class="bench-intro"><p class="eyebrow">BanditRLBench · Bandits & reinforcement learning</p>'
            '<h1>Knowledge.<br>Reasoning.<br><em>Verified action.</em></h1><p>Evaluate AI on sequential-learning mathematics, with and without Lean.</p>'
            '<p class="bench-edition">Development edition · 4 cores · 2 Lean warmups · Agentic suite under construction</p></section>'
            '<div class="bench-graph-doors">'+graphs+'</div><div class="bench-paths">'+cards+'</div>'
            '<nav class="bench-actions" aria-label="Get started"><a class="button primary" href="run/index.html">Run & train →</a><a class="button" href="review/index.html">Review & contribute →</a><a class="button" href="protocol/index.html">Task protocol →</a></nav>'
            '<details class="reader-depth"><summary>Release scope, data and evidence</summary><p>Four public dev cores; two library-application Lean companions. These are warmups, not a released agentic suite. Independent gold admission, held-out tests and model scores remain pending.</p>'
            '<p><a href="non-lean-prompts.jsonl">NL prompts</a> · <a href="lean-prompts.jsonl">Lean prompts</a> · <a href="graph-locations.json">Graph locations</a></p><p><a href="cores.json">Public solutions and rubrics</a> · <a href="Reference.lean">Reference proofs</a> · <a href="reference-replay.json">Compilation evidence</a></p></details>')


def fold_sections(body):
    def fold(m):
        section=m.group(0)
        title=re.search(r'<h2>(.*?)</h2>',section)
        if not title:
            return section
        return '<details class="reader-depth"><summary>'+title[1]+'</summary>'+section+'</details>'
    return re.sub(r'<section><h2>[\s\S]*?</section>',fold,body)


def protocol_page():
    return ('<section class="bench-intro"><p class="eyebrow">BanditRLBench · Protocol v1</p><h1>Tasks that test<br><em>mathematical work.</em></h1><p>One task family. Explicit access. Inspectable evidence.</p></section>'
            '<div class="bench-pipeline" aria-label="Task admission pipeline">'+''.join('<div><span>'+str(i)+'</span><strong>'+title+'</strong><small>'+note+'</small></div>' for i,(title,note) in enumerate([
                ('Specify','Question · source · graph'),('Verify','Reference · negative controls'),('Review','Independent semantic audit'),('Release','Frozen suite · reproducible trials')],1))+'</div>'
            '<p class="callout">Agentic Lean requires multi-step tool use: inspect the library, construct or repair a proof, compile, and retain a trajectory. Existing one-line lemma applications remain warmups.</p>'
            '<details class="reader-depth"><summary>Three abilities, two answer formats</summary><p>Knowledge: definitions and assumptions. Reasoning: derivations, counterexamples and critique. Agentic Lean: environment exploration, lemma discovery, proof repair or construction and kernel verification. Natural-language and Lean are answer formats; they are not difficulty levels.</p></details>'
            '<details class="reader-depth"><summary>Task package and automatic intake</summary><pre><code>python tools/bench_task_contract.py scaffold --id BRB-DRAFT-001 --ability agentic-lean --output _out/task-draft\npython tools/bench_task_contract.py validate _out/task-draft</code></pre><p>A draft package separates agent instructions, environment, evaluator and reference solution. Intake validates structure and hashes; it does not establish mathematical correctness or admission.</p></details>'
            '<details class="reader-depth"><summary>What every future task must supply</summary><p>Immutable source and question contract; licensing scope; stable Lean Graph anchors with relation types; family-level split and solution aliases; explicit permitted tools and retrieval access; pinned environment and budgets; answer artifact; reference solution; negative controls; independent review; verifier evidence and trajectories.</p></details>'
            '<details class="reader-depth"><summary>Evaluation and release rules</summary><p>Keep knowledge, reasoning and agentic results separate. Separate closed-book, text, graph and Lean-assisted access. Report per-family results, failures, repeated trials, token/query/tool/time budgets and the exact model/agent versions. Human rubric judgment, kernel acceptance and source fidelity are distinct. No public score before gold admission, leakage review and replicated reference/no-op controls.</p><p>Agent code must run in an isolated environment with verifier/solutions outside its accessible filesystem. Local trusted replay is not that environment; Harbor compatibility and container verification remain unreleased.</p></details>'
            '<p><a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/main/benchmarks/banditrlbench/TASK_PROTOCOL.md">Full contributor protocol →</a> · <a href="../run/index.html">Run existing warmups →</a></p>')
