from common import *
fixed()
psi='(fun z : ℝ => z ^ 4 / 4 + z ^ 2 / 2)'
q='(fun z : ℝ => z ^ 2 / 2)'
headers=[
 'theorem nonquadratic_nonsmooth :\n    StrictConvexOn ℝ univ '+psi+' ∧\n      IsMinOn (fun z : ℝ => |z| + divergence '+psi+' z (1 / 2)) univ 0 ∧\n      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧\n      divergence '+psi+' (1 / 2) 0 = 9 / 64 ∧\n      divergence '+psi+' 0 (1 / 2) = 11 / 64 ∧\n      (∀ u : ℝ, -|u| ≤ divergence '+psi+' u (1 / 2) -\n        divergence '+psi+' u 0 - divergence '+psi+' 0 (1 / 2)) ∧\n      (-1 / 2 : ℝ) ≤ -5 / 16',
 'theorem boundary_outside_initial :\n    StrictConvexOn ℝ univ '+q+' ∧\n      (-1 : ℝ) ∉ Icc 0 1 ∧\n      IsMinOn (fun z : ℝ => |z| + divergence '+q+' z (-1)) (Icc 0 1) 0 ∧\n      divergence '+q+' 0 (-1) = 1 / 2 ∧\n      (∀ u ∈ Icc (0 : ℝ) 1, -|u| ≤ divergence '+q+' u (-1) -\n        divergence '+q+' u 0 - divergence '+q+' 0 (-1)) ∧\n      (-1 / 2 : ℝ) ≤ 1 / 2'
]
neutral='import BanditRLProof.OnlineBregmanProximal\nimport Mathlib.Analysis.Calculus.Deriv.Abs\nimport Mathlib.Analysis.Convex.Mul\nopen Set BanditRL.OnlineBregman\nnamespace BanditRL.OnlineBregmanCanary\n\n'+'\n\n'.join(headers)+'\n\nend BanditRL.OnlineBregmanCanary\n'
write(RUN/'canary-neutral-types-v1.txt',neutral)
write(CONTRACT/'canary-targets-draft-v1.json',dict(stage='draft',targets=[dict(declaration='BanditRL.OnlineBregmanCanary.'+h.split()[1],exact_proposed_header=h,statement_hash=hashlib.sha256(h.encode('utf8')).hexdigest(),file='Tests/OnlineBregmanProximalCanary.lean') for h in headers],neutral_sha256=sha(RUN/'canary-neutral-types-v1.txt'),planned_consumers=['BanditRL.OnlineBregman.proximal_one_step','BanditRL.OnlineBregman.divergence_nonneg','BanditRL.OnlineBregman.divergence_eq_gradient'],body_requirement='Prove actual displayed minima and strict convexity locally. Universal comparisons invoke exact public proximal_one_step. Each final numeric conjunction branch retains that compiled production theorem in its VALUE expression via equality transport from the universal bound, rather than independently proving the true numeric inequality.',boundary='Explicit illustrative real instances, not additional printed source results, algorithm/existence or full source closure.',source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Two exact public canary types drafted; no Test body written.')
