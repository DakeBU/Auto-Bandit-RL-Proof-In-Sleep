import Tests.OnlinePrescientLinearCanary
noncomputable section
open Set Finset
open scoped InnerProductSpace
open BanditRL.OnlinePrescientLinear Tests.OnlinePrescientLinear
namespace Audit.PrescientCanary
def publicCanaryValue1 :
    prediction interval (1 / 2) signals 1 0 = -1 ∧
    prediction interval (1 / 2) signals 1 1 = -(1 / 2) ∧
    regret interval (1 / 2) signals 1 0 2 = -(11 / 2) ∧
    (∑ t ∈ range 2,
      ‖prediction interval (1 / 2) signals 1 t - iterate interval (1 / 2) signals 1 t‖ ^ 2) =
        17 / 4 ∧
    ‖iterate interval (1 / 2) signals 1 2 - 0‖ ^ 2 = 1 / 4 ∧
    ‖(1 : ℝ) - 0‖ ^ 2 / (2 * (1 / 2)) -
      ‖iterate interval (1 / 2) signals 1 2 - 0‖ ^ 2 / (2 * (1 / 2)) -
      (∑ t ∈ range 2,
        ‖prediction interval (1 / 2) signals 1 t - iterate interval (1 / 2) signals 1 t‖ ^ 2) /
          (2 * (1 / 2)) = -(7 / 2) :=
  Tests.OnlinePrescientLinear.active_projection_values

#print axioms publicCanaryValue1
#print axioms Tests.OnlinePrescientLinear.active_projection_values
#check @Tests.OnlinePrescientLinear.active_projection_values

def publicCanaryValue2 :
    (∀ (t : ℕ) (x : ℝ),
      gradient (fun w : ℝ => inner ℝ (signals t) w) x = signals t) ∧
    (‖(1 : ℝ) - 0‖ ^ 2 / (2 * (1 / 2)) -
      ‖iterate interval (1 / 2) signals 1 2 - 0‖ ^ 2 / (2 * (1 / 2)) -
      (1 / 2) / 2 * (∑ t ∈ range 2, ‖signals t‖ ^ 2)) = -(17 / 2) ∧
    ¬ (regret interval (1 / 2) signals 1 0 2 ≤
      ‖(1 : ℝ) - 0‖ ^ 2 / (2 * (1 / 2)) -
        ‖iterate interval (1 / 2) signals 1 2 - 0‖ ^ 2 / (2 * (1 / 2)) -
        (1 / 2) / 2 * (∑ t ∈ range 2, ‖signals t‖ ^ 2)) :=
  Tests.OnlinePrescientLinear.constrained_gradient_sign_counterexample

#print axioms publicCanaryValue2
#print axioms Tests.OnlinePrescientLinear.constrained_gradient_sign_counterexample
#check @Tests.OnlinePrescientLinear.constrained_gradient_sign_counterexample

def publicCanaryValue3 :
    prediction whole (1 / 2) signals 1 0 = -2 ∧
    prediction whole (1 / 2) signals 1 1 = -(3 / 2) ∧
    regret whole (1 / 2) signals 1 0 2 = -(21 / 2) ∧
    regret whole (1 / 2) signals 1 0 2 =
      ‖(1 : ℝ) - 0‖ ^ 2 / (2 * (1 / 2)) -
        ‖iterate whole (1 / 2) signals 1 2 - 0‖ ^ 2 / (2 * (1 / 2)) -
        (1 / 2) / 2 * (∑ t ∈ range 2, ‖signals t‖ ^ 2) :=
  Tests.OnlinePrescientLinear.unbounded_exact_identity

#print axioms publicCanaryValue3
#print axioms Tests.OnlinePrescientLinear.unbounded_exact_identity
#check @Tests.OnlinePrescientLinear.unbounded_exact_identity

def publicCanaryValue4 :
    prediction interval (1 / 2) signals 1 0 ≠
      prediction interval (1 / 2) (fun _ => 0) 1 0 ∧
    ∀ h : ℕ → ℝ, h 0 = 6 → prediction interval (1 / 2) h 1 0 = -1 :=
  Tests.OnlinePrescientLinear.current_and_future_information

#print axioms publicCanaryValue4
#print axioms Tests.OnlinePrescientLinear.current_and_future_information
#check @Tests.OnlinePrescientLinear.current_and_future_information

def publicCanaryValue5 :
    (3 : ℝ) ∉ interval.carrier ∧
    prediction interval 1 (fun _ => 0) 3 0 = 1 ∧
    ‖prediction interval 1 (fun _ => 0) 3 0 - iterate interval 1 (fun _ => 0) 3 0‖ ^ 2 = 4 ∧
    regret interval 1 (fun _ => 0) 3 0 0 = 0 ∧
    ∀ u ∈ interval.carrier,
      regret interval 1 (fun _ => 0) 3 u 0 ≤ ‖(3 : ℝ) - u‖ ^ 2 / (2 * 1) -
        ‖iterate interval 1 (fun _ => 0) 3 0 - u‖ ^ 2 / (2 * 1) -
        (∑ t ∈ range 0,
          ‖prediction interval 1 (fun _ => 0) 3 t - iterate interval 1 (fun _ => 0) 3 t‖ ^ 2) /
            (2 * 1) :=
  Tests.OnlinePrescientLinear.outside_initial_center_and_empty_horizon

#print axioms publicCanaryValue5
#print axioms Tests.OnlinePrescientLinear.outside_initial_center_and_empty_horizon
#check @Tests.OnlinePrescientLinear.outside_initial_center_and_empty_horizon

end Audit.PrescientCanary
