# Independent source/formal/reconstruction comparison packet

Created by /root/generic_source_review; run generic-source-review-20261009-01. This is a reviewer packet, not a source-blind decoder input.

## Input source-contract.md; SHA256 ad0bdfd568c49a8b6e2d91ba3ef23fe22a9e3ef12ece2be00b8593b8de9b01a4

# Absolute-error certificates and finite interval comparisons

Source: author-derived reusable mathematical interface, version 1 (2026-10-09).
This is elementary certificate transport; no new statistical bound is claimed.

For real target μ, intermediate value ν and estimate x, certificates
|ν−μ|≤b and |x−ν|≤s imply |x−μ|≤b+s by the triangle inequality.
The numbers b,s need no separate nonnegativity premise: the two certificates
already force it.

For a finite active set A of indices in Fin K, define surviving indices as
those i∈A whose upper endpoint x_i+r_i is at least every active lower endpoint
x_j−r_j. Endpoints that merely touch survive. An active maximizer of μ survives
whenever all active intervals contain their targets: x_j−r_j≤μ_j≤μ_*≤x_*+r_*.
No unique maximizer is required. If all active radii are at most r and
μ_*−μ_i>4r, then x_*−r_*≥μ_*−2r>μ_i+2r≥x_i+r_i, so i is removed.
If i is initially inactive it is already absent from the filter.

All four declarations are literal deterministic statements. K may be zero;
the two comparison theorems require a displayed active witness star, so their
premises then cannot hold. There is no random law, independence, measurability,
concentration producer, stopping claim or executable finite-bit comparison.

Actual Lean parents are Mathlib abs_add_le, abs_le, Finset membership/filter,
ring and linear arithmetic. The interval filter is a literal finite predicate;
it introduces no choice or default target. Its two real consumers are
optimal_survives and large_gap_removed. No existing source theorem is repaired.
The module belongs to reusable confidence infrastructure. Teaching-route,
results, roadmap and conceptual hypergraph remain unchanged with this scope:
no downstream algorithm or rate is completed. Module imports are not theorem
implications.


## Input source-topology.json; SHA256 ccac4e0745dc08b324c7f08ca17fdf2120de3b2ae8441103cb3e9050917747d5

{
  "schema_version": "source-proof-topology/v1",
  "reconstruction": {
    "method": "Independent reconstruction from the specified source-contract.md only; no Lean, formal packets, folded lessons, publication registry, other workspace, or previous research inspected.",
    "authority": "Author-derived reusable library contract; not an asserted external paper theorem.",
    "bounded_exhaustive": true,
    "approval_status": "PENDING_DISTINCT_REVIEW",
    "self_approved": false
  },
  "dependency_semantics": {
    "rule": "Each dependencies array is an AND group: all listed ingredients are used together. Dependencies are proof ingredients, not module-import implications.",
    "node_kinds": [
      "definition",
      "source_assumption",
      "derived_ingredient",
      "statement",
      "ambient_prerequisite"
    ],
    "excluded_rule": "EXCLUDED entries are provenance, scope constraints, or implementation/publication metadata, not theorem conclusions."
  },
  "source": {
    "path": "C:/qb261009/pb/docs/confidence-intervals/source-contract.md",
    "sha256": "ad0bdfd568c49a8b6e2d91ba3ef23fe22a9e3ef12ece2be00b8593b8de9b01a4",
    "version": "1 (2026-10-09)",
    "line_count": 31
  },
  "nodes": [
    {
      "id": "pb.real_setting",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        6,
        9
      ],
      "statement": "μ, ν, x, b, s are real numbers.",
      "dependencies": []
    },
    {
      "id": "pb.bias_certificate",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        6,
        7
      ],
      "statement": "|ν−μ| ≤ b.",
      "dependencies": [
        "pb.real_setting"
      ]
    },
    {
      "id": "pb.estimation_certificate",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        6,
        7
      ],
      "statement": "|x−ν| ≤ s.",
      "dependencies": [
        "pb.real_setting"
      ]
    },
    {
      "id": "pb.absolute_value_laws",
      "classification": "NODE",
      "kind": "ambient_prerequisite",
      "source_lines": [
        7,
        9
      ],
      "statement": "Triangle inequality, nonnegativity of absolute value, and |a|≤r iff −r≤a≤r over the reals.",
      "dependencies": [],
      "status": "Standard mathematics cited by the prose; not a newly proved source theorem."
    },
    {
      "id": "pb.certificate_radii_nonnegative",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        8,
        9
      ],
      "statement": "The two certificates imply 0≤b and 0≤s.",
      "dependencies": [
        "pb.bias_certificate",
        "pb.estimation_certificate",
        "pb.absolute_value_laws"
      ],
      "separate_public_premise": false
    },
    {
      "id": "pb.error_decomposition",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        6,
        7
      ],
      "statement": "x−μ = (x−ν)+(ν−μ).",
      "dependencies": [
        "pb.real_setting"
      ],
      "proof": "Real additive identity implicit in the stated triangle-inequality argument."
    },
    {
      "id": "pb.absolute_error_transport",
      "classification": "NODE",
      "kind": "statement",
      "source_lines": [
        6,
        7
      ],
      "statement": "|x−μ| ≤ b+s.",
      "dependencies": [
        "pb.bias_certificate",
        "pb.estimation_certificate",
        "pb.error_decomposition",
        "pb.absolute_value_laws"
      ],
      "proof": "Apply the triangle inequality to the decomposition and add the certificate bounds.",
      "declaration_role": "First of the source's four declarations; no separate nonnegativity premise."
    },
    {
      "id": "pb.finite_interval_setting",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        11,
        17
      ],
      "statement": "K is a natural number, A is a finite set of indices in Fin K, and μ_i, x_i, r_i are real-valued indexed families.",
      "dependencies": []
    },
    {
      "id": "pb.endpoints",
      "classification": "NODE",
      "kind": "definition",
      "source_lines": [
        12,
        14
      ],
      "statement": "L_i = x_i−r_i and H_i = x_i+r_i.",
      "dependencies": [
        "pb.finite_interval_setting"
      ]
    },
    {
      "id": "pb.interval_filter",
      "classification": "NODE",
      "kind": "definition",
      "source_lines": [
        11,
        13
      ],
      "statement": "Survive(A) = {i∈A | ∀j∈A, L_j≤H_i}.",
      "dependencies": [
        "pb.endpoints"
      ],
      "declaration_role": "Second of the source's four declarations.",
      "scope": "Literal finite predicate. Neither a chosen/default target nor an executable finite-bit comparison is supplied."
    },
    {
      "id": "pb.touching_survives",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        13,
        13
      ],
      "statement": "Endpoint equality satisfies the corresponding filter comparison; if all active lower endpoints are ≤H_i, equality in any comparison does not exclude i.",
      "dependencies": [
        "pb.interval_filter"
      ],
      "qualification": "Touching one endpoint alone does not imply survival unless every required comparison holds."
    },
    {
      "id": "pb.active_star",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        13,
        21
      ],
      "statement": "A displayed index star belongs to A.",
      "dependencies": [
        "pb.finite_interval_setting"
      ],
      "applies_to": [
        "pb.optimal_survives",
        "pb.large_gap_removed"
      ]
    },
    {
      "id": "pb.active_maximizer",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        13,
        15
      ],
      "statement": "For every j∈A, μ_j≤μ_star.",
      "dependencies": [
        "pb.active_star"
      ],
      "uniqueness_required": false,
      "applies_to": [
        "pb.optimal_survives"
      ]
    },
    {
      "id": "pb.active_containment",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        14,
        16
      ],
      "statement": "For every j∈A, L_j≤μ_j≤H_j.",
      "dependencies": [
        "pb.endpoints"
      ],
      "interpretation": "The large-gap paragraph continues the interval-containment setting introduced in the preceding sentence; it is needed to justify both outer inequalities in its displayed chain.",
      "applies_to": [
        "pb.optimal_survives",
        "pb.large_gap_removed"
      ]
    },
    {
      "id": "pb.survival_chain",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        14,
        14
      ],
      "statement": "For every j∈A, L_j≤μ_j≤μ_star≤H_star.",
      "dependencies": [
        "pb.active_containment",
        "pb.active_maximizer",
        "pb.active_star"
      ]
    },
    {
      "id": "pb.optimal_survives",
      "classification": "NODE",
      "kind": "statement",
      "source_lines": [
        13,
        15
      ],
      "statement": "star∈Survive(A).",
      "dependencies": [
        "pb.interval_filter",
        "pb.active_star",
        "pb.survival_chain"
      ],
      "proof": "For arbitrary active j, use the displayed chain, then satisfy every comparison of the finite filter.",
      "declaration_role": "Third of the source's four declarations.",
      "uniqueness_required": false
    },
    {
      "id": "pb.uniform_radius_bound",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        15,
        16
      ],
      "statement": "r is real and ∀j∈A, r_j≤r.",
      "dependencies": [
        "pb.finite_interval_setting"
      ]
    },
    {
      "id": "pb.gap_certificate",
      "classification": "NODE",
      "kind": "source_assumption",
      "source_lines": [
        15,
        16
      ],
      "statement": "For the compared index i, μ_star−μ_i>4r.",
      "dependencies": [
        "pb.finite_interval_setting"
      ]
    },
    {
      "id": "pb.inactive_absent",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        17,
        17
      ],
      "statement": "If i∉A, then i∉Survive(A).",
      "dependencies": [
        "pb.interval_filter"
      ]
    },
    {
      "id": "pb.active_radius_nonnegative",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        14,
        16
      ],
      "statement": "Containment implies 0≤r_j for j∈A; an active star and the uniform bound then imply 0≤r.",
      "dependencies": [
        "pb.active_containment",
        "pb.active_star",
        "pb.uniform_radius_bound"
      ],
      "separate_public_premise": false,
      "proof": "L_j≤H_j yields 2r_j≥0. Apply this at star and r_star≤r.",
      "status": "Implicit consequence; no new declaration inferred."
    },
    {
      "id": "pb.separated_endpoint_chain",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        16,
        16
      ],
      "statement": "If i∈A, then L_star≥μ_star−2r>μ_i+2r≥H_i.",
      "dependencies": [
        "pb.active_containment",
        "pb.active_star",
        "pb.uniform_radius_bound",
        "pb.gap_certificate"
      ],
      "proof": "Containment gives x_star≥μ_star−r_star and x_i≤μ_i+r_i; apply the radius bound and rearrange the strict gap. The middle inequality is strict."
    },
    {
      "id": "pb.active_gap_exclusion",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        16,
        16
      ],
      "statement": "If i∈A, then i∉Survive(A), because active j=star violates L_j≤H_i.",
      "dependencies": [
        "pb.interval_filter",
        "pb.active_star",
        "pb.separated_endpoint_chain"
      ]
    },
    {
      "id": "pb.large_gap_removed",
      "classification": "NODE",
      "kind": "statement",
      "source_lines": [
        15,
        17
      ],
      "statement": "i∉Survive(A), whether i is initially active or inactive.",
      "dependencies": [
        "pb.inactive_absent",
        "pb.active_gap_exclusion"
      ],
      "proof": "Split on i∈A. Use endpoint separation in the active case and filter membership in the inactive case.",
      "declaration_role": "Fourth of the source's four declarations.",
      "assumptions_inherited": [
        "pb.active_containment",
        "pb.active_star",
        "pb.uniform_radius_bound",
        "pb.gap_certificate"
      ],
      "maximizer_dependency": "The active-maximizer property belongs to the surrounding optimal-survival setting but is not used in the displayed large-gap proof. Only an active comparison witness is used."
    },
    {
      "id": "pb.zero_index_guard",
      "classification": "NODE",
      "kind": "derived_ingredient",
      "source_lines": [
        19,
        21
      ],
      "statement": "K=0 is permitted; an active star is impossible then, so neither comparison theorem has satisfiable premises.",
      "dependencies": [
        "pb.finite_interval_setting",
        "pb.active_star"
      ],
      "proof": "Fin 0 is empty, hence no element belongs to A."
    }
  ],
  "exclusions": [
    {
      "id": "pb.title",
      "classification": "EXCLUDED",
      "source_lines": [
        1,
        1
      ],
      "text": "Absolute-error certificates and finite interval comparisons",
      "reason": "Title; its mathematical content is expanded in nodes."
    },
    {
      "id": "pb.provenance",
      "classification": "EXCLUDED",
      "source_lines": [
        3,
        4
      ],
      "text": "Author-derived reusable mathematical interface, version/date; elementary certificate transport and no new statistical bound.",
      "reason": "Provenance and claim scope; no statistical theorem or external source attribution."
    },
    {
      "id": "pb.deterministic_scope",
      "classification": "EXCLUDED",
      "source_lines": [
        19,
        22
      ],
      "text": "All four declarations are deterministic; no random law, independence, measurability, concentration producer, stopping claim, or executable finite-bit comparison.",
      "reason": "Scope restriction. The K=0 mathematical guard is separately represented by pb.zero_index_guard."
    },
    {
      "id": "pb.implementation_parent_metadata",
      "classification": "EXCLUDED",
      "source_lines": [
        24,
        25
      ],
      "text": "Mathlib abs_add_le, abs_le, Finset membership/filter, ring and linear arithmetic.",
      "reason": "Source-reported implementation metadata only. No implementation inspected and no import edge asserted; abstract mathematical laws appear separately."
    },
    {
      "id": "pb.filter_scope_metadata",
      "classification": "EXCLUDED",
      "source_lines": [
        25,
        27
      ],
      "text": "Literal finite predicate with no choice/default target and two consumers optimal_survives, large_gap_removed.",
      "reason": "Scope/consumer-name metadata; definition and both mathematical consumers are represented as nodes."
    },
    {
      "id": "pb.publication_scope",
      "classification": "EXCLUDED",
      "source_lines": [
        27,
        31
      ],
      "text": "No source theorem repair; reusable confidence infrastructure; teaching-route, results, roadmap and conceptual hypergraph unchanged; no downstream algorithm/rate completed; imports are not implications.",
      "reason": "Publication and scope metadata; does not entail downstream theorem claims."
    }
  ],
  "coverage": [
    {
      "paragraph_lines": [
        1,
        1
      ],
      "items": [
        "pb.title"
      ]
    },
    {
      "paragraph_lines": [
        3,
        4
      ],
      "items": [
        "pb.provenance"
      ]
    },
    {
      "paragraph_lines": [
        6,
        9
      ],
      "items": [
        "pb.real_setting",
        "pb.bias_certificate",
        "pb.estimation_certificate",
        "pb.absolute_value_laws",
        "pb.certificate_radii_nonnegative",
        "pb.error_decomposition",
        "pb.absolute_error_transport"
      ]
    },
    {
      "paragraph_lines": [
        11,
        17
      ],
      "items": [
        "pb.finite_interval_setting",
        "pb.endpoints",
        "pb.interval_filter",
        "pb.touching_survives",
        "pb.active_star",
        "pb.active_maximizer",
        "pb.active_containment",
        "pb.survival_chain",
        "pb.optimal_survives",
        "pb.uniform_radius_bound",
        "pb.gap_certificate",
        "pb.inactive_absent",
        "pb.active_radius_nonnegative",
        "pb.separated_endpoint_chain",
        "pb.active_gap_exclusion",
        "pb.large_gap_removed"
      ]
    },
    {
      "paragraph_lines": [
        19,
        22
      ],
      "items": [
        "pb.zero_index_guard",
        "pb.deterministic_scope"
      ]
    },
    {
      "paragraph_lines": [
        24,
        31
      ],
      "items": [
        "pb.implementation_parent_metadata",
        "pb.filter_scope_metadata",
        "pb.publication_scope"
      ]
    }
  ],
  "boundary_notes": [
    "Only four declarations are claimed by the prose. Additional nodes expose definitions, premises, standard laws, and intermediate consequences; they do not invent extra public declarations.",
    "Nonnegativity consequences are recorded but need not be inserted into the minimal proof path where algebra suffices.",
    "No assumption of independence, a random model, concentration bound producer, unique maximizer, or finite-bit evaluator is licensed."
  ]
}


## Input source-topology-review.json; SHA256 098dc5cfd6e3cf7b142d08e21b0860b6fe684418583d062350a917faa33153d3

{
  "schema_version": "independent-source-topology-review/v1",
  "reviewer_identity": "/root/generic_source_review",
  "run_id": "generic-source-review-20261009-01",
  "anti_anchored": true,
  "review_order": "Raw source-contract and independently extracted source-topology only; completed and saved before inspecting Lean, formal packet, lesson, reconstruction or publication records.",
  "source_sha256": "ad0bdfd568c49a8b6e2d91ba3ef23fe22a9e3ef12ece2be00b8593b8de9b01a4",
  "topology_sha256": "ccac4e0745dc08b324c7f08ca17fdf2120de3b2ae8441103cb3e9050917747d5",
  "verdict": "accepted",
  "bounded_exhaustive": true,
  "mathematically_valid": true,
  "coverage_review": [
    "Lines 1,3-4: title, author provenance and no-statistical-novelty scope are explicitly excluded.",
    "Lines 6-9: real setting, both certificates, their nonnegativity consequences, additive decomposition, triangle inequality and transport statement are all represented. Nonnegativity is derived rather than demanded.",
    "Lines 11-17: finite setting, both endpoints, universal active-lower-endpoint filter, equality convention, displayed active witness, maximizer, interval containment, survival chain, radius bound and strict gap are represented. The inactive case and active violating comparison jointly yield removal. Maximizer is correctly not used by removal.",
    "Lines 19-22: Fin 0 guard and all deterministic/statistical/executable exclusions are represented.",
    "Lines 24-31: reported implementation parents, two consumers and publication boundary are metadata; no imported module is promoted into a logical implication."
  ],
  "mathematical_review": "For active j, containment and maximality imply L_j <= mu_j <= mu_star <= H_star, so star satisfies every comparison. In the active removal branch, containment and r_j <= r imply L_star >= mu_star-2r > mu_i+2r >= H_i. The strict middle comparison violates the filter at star. An inactive i is absent immediately. No uniqueness, random law, statistical producer or finite-bit evaluator is needed or inferred.",
  "dependency_review": "All dependencies resolve; the arrays are coherent AND ingredient groups. Auxiliary consequences are distinguished from the four public declarations. The large-gap statement inherits containment and an active witness, but not the unused maximality premise. Coverage accounts for every nonblank source paragraph and all scope claims.",
  "blockers": [],
  "limits": "Acceptance applies only to source-faithful mathematical topology at these hashes; no Lean correctness or chronology verdict is included."
}


## Input formal-packet.md; SHA256 447ad210c92d5963b3052c0b81afbcf82de2af6c4729696ae92b2ac26440bafc

```lean
import Mathlib.Tactic


namespace BanditRLProof.ConfidenceIntervals


theorem bias_statistical_composition {μ ν estimate b s : ℝ}
    (hb : |ν - μ| ≤ b) (hs : |estimate - ν| ≤ s) :
    |estimate - μ| ≤ b + s := by
  calc
    _ = |(estimate - ν) + (ν - μ)| := by congr 1; ring
    _ ≤ |estimate - ν| + |ν - μ| := abs_add_le _ _
    _ ≤ b + s := by linarith


noncomputable def survivors {K : ℕ} (active : Finset (Fin K))
    (estimate radius : Fin K → ℝ) : Finset (Fin K) :=
  active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i

theorem optimal_survives {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star : Fin K) (hstar : star ∈ active)
    (hopt : ∀ i ∈ active, μ i ≤ μ star)
    (hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i) :
    star ∈ survivors active estimate radius := by
  classical
  simp only [survivors, Finset.mem_filter]
  refine ⟨hstar, fun i hi => ?_⟩
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hi)).2
  linarith [hopt i hi]

theorem large_gap_removed {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star i : Fin K) (hstar : star ∈ active)
    {r : ℝ} (hwidth : ∀ j ∈ active, radius j ≤ r)
    (hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
    (hgap : 4 * r < μ star - μ i) :
    i ∉ survivors active estimate radius := by
  classical
  intro hi
  obtain ⟨hia, hkeep⟩ := Finset.mem_filter.mp hi
  have hcmp := hkeep star hstar
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hia)).2
  linarith [hwidth star hstar, hwidth i hia]

end BanditRLProof.ConfidenceIntervals
```


## Input lesson.md; SHA256 659201d18ebf1df3f67eb6e7b221d3aff035c1f54e8869282c525016cffd06c3

# Absolute-error certificates and finite interval comparisons

Source: author-derived reusable mathematical interface, version 1 (2026-10-09).
This is elementary certificate transport; no new statistical bound is claimed.

For real target μ, intermediate value ν and estimate x, certificates
|ν−μ|≤b and |x−ν|≤s imply |x−μ|≤b+s by the triangle inequality.
The numbers b,s need no separate nonnegativity premise: the two certificates
already force it.

For a finite active set A of indices in Fin K, define surviving indices as
those i∈A whose upper endpoint x_i+r_i is at least every active lower endpoint
x_j−r_j. Endpoints that merely touch survive. An active maximizer of μ survives
whenever all active intervals contain their targets: x_j−r_j≤μ_j≤μ_*≤x_*+r_*.
No unique maximizer is required. If all active radii are at most r and
μ_*−μ_i>4r, then x_*−r_*≥μ_*−2r>μ_i+2r≥x_i+r_i, so i is removed.
If i is initially inactive it is already absent from the filter.

All four declarations are literal deterministic statements. K may be zero;
the two comparison theorems require a displayed active witness star, so their
premises then cannot hold. There is no random law, independence, measurability,
concentration producer, stopping claim or executable finite-bit comparison.

Actual Lean parents are Mathlib abs_add_le, abs_le, Finset membership/filter,
ring and linear arithmetic. The interval filter is a literal finite predicate;
it introduces no choice or default target. Its two real consumers are
optimal_survives and large_gap_removed. No existing source theorem is repaired.
The module belongs to reusable confidence infrastructure. Teaching-route,
results, roadmap and conceptual hypergraph remain unchanged with this scope:
no downstream algorithm or rate is completed. Module imports are not theorem
implications.

<details><summary>Exact Lean statement and proof: BanditRLProof/ConfidenceIntervals.lean</summary>

```lean
import Mathlib.Tactic

/-! Deterministic absolute-error certificates and finite interval comparisons. -/
namespace BanditRLProof.ConfidenceIntervals

/-- Two absolute-error certificates compose by the triangle inequality. -/
theorem bias_statistical_composition {μ ν estimate b s : ℝ}
    (hb : |ν - μ| ≤ b) (hs : |estimate - ν| ≤ s) :
    |estimate - μ| ≤ b + s := by
  calc
    _ = |(estimate - ν) + (ν - μ)| := by congr 1; ring
    _ ≤ |estimate - ν| + |ν - μ| := abs_add_le _ _
    _ ≤ b + s := by linarith

/-- Strictly disjoint intervals remove arms; touching intervals and ties survive. -/
noncomputable def survivors {K : ℕ} (active : Finset (Fin K))
    (estimate radius : Fin K → ℝ) : Finset (Fin K) :=
  active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i

theorem optimal_survives {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star : Fin K) (hstar : star ∈ active)
    (hopt : ∀ i ∈ active, μ i ≤ μ star)
    (hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i) :
    star ∈ survivors active estimate radius := by
  classical
  simp only [survivors, Finset.mem_filter]
  refine ⟨hstar, fun i hi => ?_⟩
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hi)).2
  linarith [hopt i hi]

theorem large_gap_removed {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star i : Fin K) (hstar : star ∈ active)
    {r : ℝ} (hwidth : ∀ j ∈ active, radius j ≤ r)
    (hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
    (hgap : 4 * r < μ star - μ i) :
    i ∉ survivors active estimate radius := by
  classical
  intro hi
  obtain ⟨hia, hkeep⟩ := Finset.mem_filter.mp hi
  have hcmp := hkeep star hstar
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hia)).2
  linarith [hwidth star hstar, hwidth i hia]

end BanditRLProof.ConfidenceIntervals
```

</details>


## Input blind-reconstruction.md; SHA256 2ce868a540057049567ba47133ed3c283fd69ba40f89d05bf5496b4f2c5cb361

# Independent formal reconstruction: confidence intervals

Decoder identity: `/root/generic_blind_decode`.
Run ID: `generic-blind-decode-20261009-efd2870d-d7f6-4aa9-89a8-e2a410527bab`.
Only input read: `docs/confidence-intervals/formal-packet.md`.
Packet SHA256: `447ad210c92d5963b3052c0b81afbcf82de2af6c4729696ae92b2ac26440bafc`.
Source blind: true. This is a reconstruction, not a source review or acceptance verdict.

## Four declarations

All four are in `BanditRLProof.ConfidenceIntervals`. Scalars are real numbers; finite indices use `Fin K` for a natural number `K`.

### 1. `bias_statistical_composition`

Implicit binders: `{μ ν estimate b s : ℝ}`. Explicit proof arguments, in order: `(hb : |ν - μ| ≤ b)` and `(hs : |estimate - ν| ≤ s)`. Conclusion: `|estimate - μ| ≤ b + s`.

For any three real values and two real upper bounds satisfying those two absolute-error inequalities, the direct error is at most their sum. The intermediate value is `ν`. No probability space, expectation, sample, distribution, or stochastic qualification occurs. The proof is the triangle inequality after writing `estimate - μ = (estimate - ν) + (ν - μ)`.

### 2. `survivors`

This is a `noncomputable def`, not a theorem. Implicit binder: `{K : ℕ}`. Explicit arguments, in order: `(active : Finset (Fin K))` and `(estimate radius : Fin K → ℝ)`. Result type: `Finset (Fin K)`.

Its literal definition is:

```lean
active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i
```

Thus `i` survives exactly when `i ∈ active` and every active index `j` has lower endpoint `estimate j - radius j` at most the upper endpoint `estimate i + radius i`. The comparison includes `j = i`; it uses a non-strict inequality. No nonnegativity condition is imposed by the definition.

### 3. `optimal_survives`

Implicit binder: `{K : ℕ}`. Explicit binders, in order:

```lean
(active : Finset (Fin K))
(μ estimate radius : Fin K → ℝ)
(star : Fin K)
(hstar : star ∈ active)
(hopt : ∀ i ∈ active, μ i ≤ μ star)
(hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i)
```

Conclusion: `star ∈ survivors active estimate radius`.

Every active true value is bounded above by the true value at the selected active index `star`, and every active estimate has the stated absolute-error bound. Consequently every active lower endpoint lies below the upper endpoint of `star`, so that selected maximizer survives. The maximizer need not be unique. The hypotheses concern only active indices.

### 4. `large_gap_removed`

Implicit binder `{K : ℕ}`, followed by these explicit and implicit arguments in their actual order:

```lean
(active : Finset (Fin K))
(μ estimate radius : Fin K → ℝ)
(star i : Fin K)
(hstar : star ∈ active)
{r : ℝ}
(hwidth : ∀ j ∈ active, radius j ≤ r)
(hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
(hgap : 4 * r < μ star - μ i)
```

Conclusion: `i ∉ survivors active estimate radius`.

The selected comparator `star` is active, all active radii are bounded by a common real number `r`, and all active estimates satisfy the confidence inequalities. A strictly greater-than-`4r` true-value gap from `star` to `i` forces removal. Neither active membership of `i` nor global optimality of `star` is assumed. If `i` were a survivor, it would be active, allowing the confidence and width premises to be applied to it. Those bounds would force the lower endpoint of `star` strictly above the upper endpoint of `i`, contradicting the survivor comparison.

## Seven semantic slots, compared using formal content only

| Slot | Composition | Survivors definition | Optimal survives | Large gap removed |
|---|---|---|---|---|
| 1. Quantification | Five implicit reals | Implicit natural `K`; finite active set; two real functions | Implicit `K`; active set; three real functions; selected index | Implicit `K` and real `r`; active set; three functions; two indices |
| 2. Object / literal meaning | Absolute real errors through `ν` | Filter by all active lower-endpoint / candidate upper-endpoint comparisons | Membership in that literal filter | Nonmembership in that literal filter |
| 3. Required premises | Two deterministic absolute-error bounds | None | Selected index active, maximal true value on active set, all active error bounds | Comparator active, all active radius upper bounds and error bounds, strict true gap |
| 4. Claimed result | Error at most `b+s` | A finite subset of active | Selected maximizer retained | Selected candidate excluded |
| 5. Constants / inequality direction | Coefficients one; weak `≤` | Weak `≤`; all comparisons retained at equality | Weak optimality and confidence bounds | Threshold `4*r`; gap must be strict |
| 6. Scope / conventions | Real absolute value; no stochastic interpretation | `Finset (Fin K)`; candidate compared to every active index, including itself | Assumptions only on active set | Comparator need not be optimal; candidate need not initially be active |
| 7. Edge cases / limits | Premises imply `b,s ≥ 0`; no separately stated sign assumptions | Empty active yields empty survivors; negative radii allowed as input | `hstar` excludes empty active and makes `K=0` unavailable; ties allowed; confidence implies active radii nonnegative | `hstar` and confidence/width imply `r ≥ 0`; inactive candidates are already absent; equality of the gap to `4*r` gives no removal claim |

For `r=0`, all active error bounds and widths force exact estimates and zero active radii. The removal theorem then applies to every strictly positive comparator gap. Nothing is asserted about inactive estimates, radii, or true values except where they appear as the candidate gap. For `K=0`, there are no indices to instantiate the last two statements; the definition still accepts the empty active set.

## What these declarations do not prove

They do not establish how an estimate or radius is obtained, that any error bound holds with a particular probability, a uniform-in-time event, concentration, sampling independence, a sample budget, termination, regret, or identification guarantees for an algorithm. They do not prove uniqueness of an optimum, strict separation at the exact `4*r` threshold, that every retained index is optimal, or that every removed index is suboptimal without the displayed comparator and gap premises. The definitions and theorems are bounded deterministic real inequalities and finite-set facts.


## Input port-statement-seal.json; SHA256 1816458f1ff55dc9d937fb12438ba11fed2876cf944afb2d02429acb8809e24e

{
  "phase": "exact clean-port signature audit corrected after port; not a fresh pre-proof Source-Anchor seal",
  "sources": "author-derived generic mathematical contracts; no research objective or algorithm source attribution",
  "typing": "finite carriers, decidable equality and real/complex spaces",
  "source_inputs": "only the explicitly displayed error certificates, interval coverage, maximizer, normalized state, unitaries and effect bounds",
  "derived_not_inputs": [
    "effect contraction from Loewner bounds",
    "output normalization from unitarity",
    "circuit unitary and aligned circuit perturbation from existing library producers"
  ],
  "definition_audit": "literal probability formula and literal weak endpoint interval comparisons; strict removal of disjoint intervals. No new characterized choice object.",
  "scope_boundary": "no estimator, stochastic independence, complexity or physical runtime theorem",
  "signatures": [
    {
      "module": "BanditRLProof/ConfidenceIntervals.lean",
      "signature": "theorem bias_statistical_composition {\u03bc \u03bd estimate b s : \u211d}\n    (hb : |\u03bd - \u03bc| \u2264 b) (hs : |estimate - \u03bd| \u2264 s) :\n    |estimate - \u03bc| \u2264 b + s",
      "sha256": "21a5200d4a35d9a3a16e3d47136d4d3bcb9fd752bdcf37a5670582cc77894478"
    },
    {
      "module": "BanditRLProof/ConfidenceIntervals.lean",
      "signature": "noncomputable def survivors {K : \u2115} (active : Finset (Fin K))\n    (estimate radius : Fin K \u2192 \u211d) : Finset (Fin K)",
      "sha256": "6210f72442fd672c73f4e3ead83bfc6eb9aebb7345a15657bee7765f54ec808a"
    },
    {
      "module": "BanditRLProof/ConfidenceIntervals.lean",
      "signature": "theorem optimal_survives {K : \u2115} (active : Finset (Fin K))\n    (\u03bc estimate radius : Fin K \u2192 \u211d) (star : Fin K) (hstar : star \u2208 active)\n    (hopt : \u2200 i \u2208 active, \u03bc i \u2264 \u03bc star)\n    (hconf : \u2200 i \u2208 active, |estimate i - \u03bc i| \u2264 radius i) :\n    star \u2208 survivors active estimate radius",
      "sha256": "8481cb5c5c16ecf3d027c59f4eab712cc43d5a5ff811660a01f0eb9a54efbe3c"
    },
    {
      "module": "BanditRLProof/ConfidenceIntervals.lean",
      "signature": "theorem large_gap_removed {K : \u2115} (active : Finset (Fin K))\n    (\u03bc estimate radius : Fin K \u2192 \u211d) (star i : Fin K) (hstar : star \u2208 active)\n    {r : \u211d} (hwidth : \u2200 j \u2208 active, radius j \u2264 r)\n    (hconf : \u2200 j \u2208 active, |estimate j - \u03bc j| \u2264 radius j)\n    (hgap : 4 * r < \u03bc star - \u03bc i) :\n    i \u2209 survivors active estimate radius",
      "sha256": "5e75328578ffc45f2970ba26de31c645d05c6c04de94db0edb8c22649157fb12"
    }
  ],
  "declaration_level": "Canonical reusable library nodes and their internal providers; no external-paper or new-research-result source anchor.",
  "chronology_boundary": "Proof artifacts already existed. The v1 export is retained as superseded-invalid evidence. This v2 audit repairs metadata only; no mathematical signature was modified, and no retrospective proof-development chronology is asserted. Canonical reusable node status is separate from a fresh Source Anchor lifecycle.",
  "schema_version": 2
}


## Actual module BanditRLProof\ConfidenceIntervals.lean; SHA256 5acacb65643d0b2facc23d2ded935a1c3212aa5d13b6e5c548a0d9fa4a6e88d6

import Mathlib.Tactic

/-! Deterministic absolute-error certificates and finite interval comparisons. -/
namespace BanditRLProof.ConfidenceIntervals

/-- Two absolute-error certificates compose by the triangle inequality. -/
theorem bias_statistical_composition {μ ν estimate b s : ℝ}
    (hb : |ν - μ| ≤ b) (hs : |estimate - ν| ≤ s) :
    |estimate - μ| ≤ b + s := by
  calc
    _ = |(estimate - ν) + (ν - μ)| := by congr 1; ring
    _ ≤ |estimate - ν| + |ν - μ| := abs_add_le _ _
    _ ≤ b + s := by linarith

/-- Strictly disjoint intervals remove arms; touching intervals and ties survive. -/
noncomputable def survivors {K : ℕ} (active : Finset (Fin K))
    (estimate radius : Fin K → ℝ) : Finset (Fin K) :=
  active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i

theorem optimal_survives {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star : Fin K) (hstar : star ∈ active)
    (hopt : ∀ i ∈ active, μ i ≤ μ star)
    (hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i) :
    star ∈ survivors active estimate radius := by
  classical
  simp only [survivors, Finset.mem_filter]
  refine ⟨hstar, fun i hi => ?_⟩
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hi)).2
  linarith [hopt i hi]

theorem large_gap_removed {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star i : Fin K) (hstar : star ∈ active)
    {r : ℝ} (hwidth : ∀ j ∈ active, radius j ≤ r)
    (hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
    (hgap : 4 * r < μ star - μ i) :
    i ∉ survivors active estimate radius := by
  classical
  intro hi
  obtain ⟨hia, hkeep⟩ := Finset.mem_filter.mp hi
  have hcmp := hkeep star hstar
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hia)).2
  linarith [hwidth star hstar, hwidth i hia]

end BanditRLProof.ConfidenceIntervals
