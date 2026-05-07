/-
# Actor–critic two-timescale convergence — ABLATION target
#
# This file is used by the `I5a_ablation` fleet target. It
# contains ONLY the original (as-commonly-stated) two-timescale
# actor–critic convergence theorem, with no summability
# hypotheses, no helper lemmas, and no prose pointing at the
# counterexample. The statement is presented as-if it were a
# textbook Konda–Tsitsiklis retelling we are asked to close.
#
# The fleet's job is to decide whether to close the theorem, or
# to produce a counterexample showing it is false as stated.
-/
import CreditAssignment.ActorCritic

namespace CreditAssignment
namespace ActorCritic

open CreditAssignment.ActorCritic

/-- Two-timescale actor–critic convergence (as commonly retold
    from Konda & Tsitsiklis, 2000 and Borkar, 2008).
    Given bounded rewards, Robbins–Monro step sizes with
    α_θ(t) / α_w(t) → 0, γλ < 1, and a trajectory, the actor
    and critic iterates converge. -/
theorem actor_critic_two_timescale_converges_ablation
    {d : ℕ}
    (αw αθ : StepSize) (γ : Discount) (lam : Lambda)
    (hgl : γ.val * lam.val < 1)
    (h_two_timescale :
      Filter.Tendsto (fun t : ℕ => αθ.seq t / αw.seq t)
        Filter.atTop (nhds 0))
    (τ : Trajectory) (hBounded : BoundedReward τ)
    (ψ : State → Action → Fin d → ℝ)
    (V₀ : ValueFn) (θ₀ : Fin d → ℝ)
    (V_iter : ℕ → ValueFn) (θ_iter : ℕ → Fin d → ℝ)
    (hV_init : V_iter 0 = V₀) (hθ_init : θ_iter 0 = θ₀)
    (h_critic_update :
      ∀ t, V_iter (t + 1) = criticUpdate αw γ lam (V_iter t) τ t)
    (h_actor_update :
      ∀ t, θ_iter (t + 1) =
        actorUpdate αθ γ ψ (V_iter t) (θ_iter t) τ t) :
    ∃ (V_star : ValueFn) (θ_star : Fin d → ℝ),
      (∀ s : State,
        Filter.Tendsto
          (fun t : ℕ => V_iter t s) Filter.atTop (nhds (V_star s)))
      ∧ (∀ i : Fin d,
        Filter.Tendsto
          (fun t : ℕ => θ_iter t i) Filter.atTop (nhds (θ_star i))) := by
  sorry

end ActorCritic
end CreditAssignment
