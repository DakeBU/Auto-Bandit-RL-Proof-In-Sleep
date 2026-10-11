from pathlib import Path
import hashlib,json
R=Path('E:/ABRL/worktrees/research-online-book');P=Path(__file__).resolve().parent
auth=R/'tmp/online-b4-next-stability-freeze-20261012/body-construction-authorization-v1.json'
assert hashlib.sha256(auth.read_bytes()).hexdigest()=='3906fe82d8993bae5c0fba5d053c0c710521eb5e9c9c55b9bb595bd55773e7d3'
H=R/'tmp/online-b4-next-stability-freeze-20261012/neutral-frozen-header-v1.txt';h=H.read_text(encoding='utf-8');assert hashlib.sha256(H.read_bytes()).hexdigest()=='b713181a47d73e4858a39309986bcb6ad98e4b24bea68911b0e7f24f51cfa51b'
body=''' := by
  classical
  let G : E → EReal := fun x =>
    (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
  change (G p).toReal - (G q).toReal ≤ g (p - q) - (lam / 2) * ‖p - q‖ ^ 2
  have hfinite (i : ℕ) (hi : i < n + 1) (x : E) (hx : x ∈ V) :
      ((loss i x).toReal : EReal) = loss i x :=
    EReal.coe_toReal (ne_of_lt (hdom i hi hx)) (hbot i hi x)
  have hsumBot (m : ℕ) (hm : m ≤ n + 1) (x : E) :
      (∑ i ∈ range m, loss i x) ≠ ⊥ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      exact EReal.add_ne_bot_iff.mpr
        ⟨ih (Nat.le_trans (Nat.le_succ m) hm),
          hbot m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm) x⟩
  have hsumFinite (m : ℕ) (hm : m ≤ n + 1) (x : E) (hx : x ∈ V) :
      (∑ i ∈ range m, loss i x) = ((∑ i ∈ range m, (loss i x).toReal : ℝ) : EReal) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_range_succ, ih (Nat.le_trans (Nat.le_succ m) hm),
        ← hfinite m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm) x hx, EReal.coe_add]
      simp only [EReal.toReal_coe]
  have hvalue (x : E) (hx : x ∈ V) :
      G x = ((psi x + ∑ i ∈ range (n + 1), (loss i x).toReal : ℝ) : EReal) := by
    dsimp [G]
    rw [hsumFinite (n + 1) le_rfl x hx]
    simp only [extendedIndicator, if_pos hx, add_zero]
  have hout (x : E) (hx : x ∉ V) : G x = ⊤ := by
    dsimp [G]
    rw [show extendedIndicator V x = ⊤ by simp [extendedIndicator, hx]]
    exact EReal.add_top_of_ne_bot
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hsumBot (n + 1) le_rfl x⟩)
  have hGbot (x : E) : G x ≠ ⊥ := by
    by_cases hx : x ∈ V
    · rw [hvalue x hx]
      exact EReal.coe_ne_bot _
    · rw [hout x hx]
      exact top_ne_bot
  have hGdom : V ⊆ effectiveDomain G := by
    intro x hx
    change G x < ⊤
    rw [hvalue x hx]
    exact EReal.coe_lt_top _
  have hproper : SourceProper G := sourceProper_of_domain G V ⟨p, hp⟩ hGbot hGdom
  have hprior (x : E) (hx : x ∈ V) :
      (psi x : EReal) + ∑ i ∈ range n, loss i x + (hint x : EReal) =
        ((psi x + ∑ i ∈ range n, (loss i x).toReal + hint x : ℝ) : EReal) := by
    rw [hsumFinite n (Nat.le_succ n) x hx]
    simp only [EReal.coe_add]
  have hsupport : ∀ z ∈ V, G p + (g (z - p) : EReal) ≤ G z := by
    intro z hz
    have hm := hprediction hz
    change (psi p : EReal) + ∑ i ∈ range n, loss i p + (hint p : EReal) ≤
      (psi z : EReal) + ∑ i ∈ range n, loss i z + (hint z : EReal) at hm
    rw [hprior p hp, hprior z hz] at hm
    have hmr : psi p + ∑ i ∈ range n, (loss i p).toReal + hint p ≤
        psi z + ∑ i ∈ range n, (loss i z).toReal + hint z := by exact_mod_cast hm
    have hd := hdifference z hz
    rw [hvalue p hp, hvalue z hz, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [sum_range_succ]
    linarith [hmr, hd]
  have hb := stronglyConvex_support_growth G V lam hproper hV hGdom hlam
    hstrong p hp g hsupport q hq
  have hcancel : g (q - p) + g (p - q) = 0 := by
    simp only [map_sub]
    ring
  rw [norm_sub_rev q p] at hb
  linarith
'''
suffix='\n\nend BanditRL.OnlineConvex\n';assert h.endswith(suffix)
candidate=h[:-len(suffix)]+body+suffix
assert candidate.split(' := by\n',1)[0]+suffix==h
with (P/'candidate-v1.lean').open('xb') as f:f.write(candidate.encode())
report=dict(status='CONSTRUCTED_ONLY_NOT_ELABORATED_NOT_COMPILED',header_bytes=len(H.read_bytes()),header_sha256=hashlib.sha256(H.read_bytes()).hexdigest(),candidate_bytes=len(candidate.encode()),candidate_sha256=hashlib.sha256(candidate.encode()).hexdigest(),authorization_sha256=hashlib.sha256(auth.read_bytes()).hexdigest(),genuine_intended_parents=['sourceProper_of_domain on explicit actual G with derived inputs','stronglyConvex_support_growth on same G with produced hsupport'],hprediction='Exactly original prior-prefix-plus-hint minimization; not IsMinOn G.',support_route='Add actual prediction inequality to local loss-minus-hint support after finite-prefix conversion, cancel hint and expand range(n+1).',boundary='Finite branch conditional stability only; no attainment, dual-norm Young bound, ghost gap removal or full7.47.',Lean_processes_started=0)
with (P/'construction-report-v1.json').open('x',encoding='utf-8') as f:json.dump(report,f,indent=2)
print(json.dumps(report))
