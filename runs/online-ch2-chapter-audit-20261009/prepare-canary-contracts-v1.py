from lower_common_v1 import *
d=reviewed()
specs=[
('source_shift_ten','''theorem source_shift_ten :
    ConvexOn ℝ Set.univ (fun w : ℝ => |w - 10|) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 10 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 9 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 11'''),
('positive_negative_labels','''theorem positive_negative_labels :
    ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) (1 / 6) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) (-1 / 6) ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) 0 ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) 0 ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0)'''),
('zero_label_and_feature','''theorem zero_label_and_feature (y z : ℝ) :
    Differentiable ℝ (fun w : ℝ => max (1 - 0 * inner ℝ z w) 0) ∧
      Differentiable ℝ (fun w : ℝ => max (1 - y * inner ℝ (0 : ℝ) w) 0) ∧
      ∀ w : ℝ, max (1 - 0 * inner ℝ z w) 0 = 1 ∧
        max (1 - y * inner ℝ (0 : ℝ) w) 0 = 1'''),
('plane_ambient_and_tangential','''theorem plane_ambient_and_tangential :
    ¬ DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0)
        (e0 + (3 : ℝ) • e1) ∧
      DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0) e1 ∧
      DifferentiableAt ℝ (fun t : ℝ => max (1 - inner ℝ e0 (e0 + t • e1)) 0) 0'''),
('dimension_zero','''theorem dimension_zero (y : ℝ) (z : EuclideanSpace ℝ (Fin 0)) :
    Differentiable ℝ
        (fun w : EuclideanSpace ℝ (Fin 0) => max (1 - y * inner ℝ z w) 0) ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), max (1 - y * inner ℝ z w) 0 = 1''')]
targets=[dict(declaration='Tests.OnlineNonsmoothExamples.'+name,exact_header=header,statement_hash=statement_hash(header),
 owning_module='Tests/OnlineNonsmoothExamplesCanary.lean') for name,header in specs]
write(CONTRACT/'nonsmooth-canary-contracts-v1.json',dict(stage='frozen canary proposition proposals before any canary proof BODY',
 targets=targets,production_terminal_hashes=[t['statement_hash'] for t in d['targets']],
 actual_context=dict(imports=['BanditRLProof.OnlineNonsmoothExamples','Tests.OnlineGradientDescentSourceCanary'],
  open_scoped='InnerProductSpace',open_namespace='Tests.OnlineGradientDescentSource',
  complete_existing_context_file_sha256=sha(ROOT/'Tests/OnlineGradientDescentSourceCanary.lean'),
  canonical_reused_values=['Tests.OnlineGradientDescentSource.Plane','Tests.OnlineGradientDescentSource.e0','Tests.OnlineGradientDescentSource.e1'],
  value_definitions='Plane=EuclideanSpace real(Fin2); e0=EuclideanSpace.single0 1; e1=EuclideanSpace.single1 1; canonical existing test definitions, no duplicate per-Book geometry library.'),
 boundary='Five public complementary canary propositions, three nondegenerate examples and two explicit degenerate regimes. Not five new source theorems, not chapter coverage. Blind reconstruction and distinct actual BODY review required before acceptance.',
 chapter_complete=False,whole_Goal_status='ACTIVE'))
context='''# Neutral concrete-proposition reconstruction packet

Only read this packet and the accompanying input JSON. No source/history/repository search, proof or compilation. Reconstruct every complete terminal in prose/LaTeX/seven slots, distinguishing pointwise/global/ambient/tangential derivatives and the degenerate tests. Role history reused, not absolute blindness.

Notation: inner is the real inner product. DifferentiableAt is ordinary real ambient Fréchet differentiability at the specified point; Differentiable is at every ambient point. ConvexOn on univ is global convexity. These neutral aliases are exact mathematical values:

```lean
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def e0 : Plane := EuclideanSpace.single 0 1
def e1 : Plane := EuclideanSpace.single 1 1
open scoped InnerProductSpace
```

No additional section variables or hypotheses.

```lean
'''
for i,(name,header) in enumerate(specs,1):context+=header.replace('theorem '+name,'theorem TerminalC%03d'%i,1)+'\n\n'
context+='```\n'
write(RUN/'nonsmooth-canary-blind-packet-v1.md',context)
write(RUN/'nonsmooth-canary-blind-input-v1.json',dict(packet_path=(RUN/'nonsmooth-canary-blind-packet-v1.md').as_posix(),
 packet_sha256=sha(RUN/'nonsmooth-canary-blind-packet-v1.md'),scope='Only this neutral packet, exact aliases and input JSON. Five frozen concrete proposition proposals, no source identity, proof or previous verdict.'))
reviewed();print('Five exact canary propositions frozen before any canary BODY; reuse existing canonical real-plane values.')
