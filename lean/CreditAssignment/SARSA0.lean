/- R3. SARSA(0) — analogous to TD(0) but over (state, action). -/
import CreditAssignment.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace CreditAssignment
namespace SARSA0

open Filter Topology

noncomputable def sarsaUpdate
    (α γ : ℝ) (Q : QFn) (s : State) (a : Action) (r : Reward)
    (s' : State) (a' : Action) : QFn :=
  fun x y =>
    if x = s ∧ y = a then Q s a + α * (r + γ * Q s' a' - Q s a) else Q x y

/-- I3b one-step support. -/
theorem sarsa0_one_step_support
    (α γ : ℝ) (Q : QFn) (s : State) (a : Action) (r : Reward)
    (s' : State) (a' : Action) (x : State) (y : Action)
    (hxy : ¬ (x = s ∧ y = a)) :
    sarsaUpdate α γ Q s a r s' a' x y = Q x y := by
  unfold sarsaUpdate
  rw [if_neg hxy]

/-- Iterated SARSA(0) for a fixed trajectory + action schedule. -/
noncomputable def sarsa0Iterate
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (Q₀ : QFn) : ℕ → QFn
  | 0     => Q₀
  | t + 1 =>
      sarsaUpdate (α.seq t) γ.val
        (sarsa0Iterate α γ τ Q₀ t)
        (τ.states t) (τ.actions t) (τ.rewards t)
        (τ.states (t + 1)) (τ.actions (t + 1))

/-- **I3a. SARSA(0) convergence** (content statement). Robbins-Monro +
    bounded reward + `γ < 1` implies pointwise convergence of Q_t. -/
theorem sarsa0_converges
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (hBounded : BoundedReward τ)
    (Q₀ : QFn) :
    ∃ Q_star : QFn,
      ∀ s : State, ∀ a : Action,
        Filter.Tendsto
          (fun t : ℕ => sarsa0Iterate α γ τ Q₀ t s a)
          Filter.atTop (𝓝 (Q_star s a)) := by
  sorry -- Robbins-Monro; Mathlib upstream

end SARSA0
end CreditAssignment
