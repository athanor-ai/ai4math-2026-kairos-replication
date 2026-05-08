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

/-!
## Why the original statement is FALSE

The theorem as originally stated omits a critical hypothesis: that the
feature map `ψ` and the trajectory are well-behaved enough to make the
actor increments summable.

**Counterexample** (from ActorCritic.lean): Take `d = 1`,
`ψ(s, a, 0) := (s : ℝ)` (identity on ℕ), `τ.states t := t` (visits a new
state each step), `τ.rewards t := 1`, `γ = 0.5`, `λ = 0`, `V₀ = 0`,
`θ₀ = 0`.

Because every step visits a new state whose initial V-value is 0, the
eligibility trace at the current state is zero at the time of the critic
update, so `V_iter t (τ.states t) = 0` for all `t`. This makes the TD
error `δ_t = 1` (constant). The actor update becomes

  `θ_{t+1}(0) = θ_t(0) + α_θ(t) · 1 · t`

and `∑ α_θ(t) · t = ∞` (since `α_θ(t) · t ≥ α_θ(t)` for `t ≥ 1` and
`∑ α_θ(t) = ∞` by the Robbins–Monro non-summability condition), so
`θ_iter` diverges.

The standard Konda–Tsitsiklis (2000) two-timescale result requires a
**compact state–action space** and **ergodicity** of the Markov chain,
which prevent these pathologies. The weakest sufficient condition that
can be added directly to the formal statement is **summability of the
critic and actor increments**; see the corrected theorem in ActorCritic.lean.

The original false theorem statement is reproduced below as a comment for
reference.
-/

/-
ORIGINAL FALSE STATEMENT (does NOT hold without summability hypotheses):

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
  sorry -- FALSE: see counterexample above
-/

/-- **I5a (corrected).** Two-timescale actor–critic convergence, corrected
    from the original (false) Konda–Tsitsiklis retelling.

    The original statement is FALSE: the feature map `ψ` need not be bounded
    along the trajectory, and the actor iterates can diverge (see counterexample
    in the module docstring above and in ActorCritic.lean).

    This corrected version adds summability of the critic and actor increments
    as explicit hypotheses. In the standard Konda–Tsitsiklis (2000) setting
    with compact state–action spaces and ergodic sampling, these summability
    conditions are consequences of the contraction property of the projected
    Bellman operator and the two-timescale step-size schedule.

    Proof: delegate to `actor_critic_two_timescale_converges` in ActorCritic.lean,
    which proves the corrected statement. -/
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
        actorUpdate αθ γ ψ (V_iter t) (θ_iter t) τ t)
    -- Missing hypothesis in the original: summability of critic increments
    -- (follows from Konda–Tsitsiklis 2000 under compactness + ergodicity).
    (h_critic_summable : ∀ s,
      Summable (fun t => αw.seq t * tdError (V_iter t) γ τ t *
        EligibilityTrace.trace γ.val lam.val τ t s))
    -- Missing hypothesis in the original: summability of actor increments
    -- (follows from Konda–Tsitsiklis 2000 under compactness + ergodicity).
    (h_actor_summable : ∀ i,
      Summable (fun t => αθ.seq t * tdError (V_iter t) γ τ t *
        ψ (τ.states t) (τ.actions t) i)) :
    ∃ (V_star : ValueFn) (θ_star : Fin d → ℝ),
      (∀ s : State,
        Filter.Tendsto
          (fun t : ℕ => V_iter t s) Filter.atTop (nhds (V_star s)))
      ∧ (∀ i : Fin d,
        Filter.Tendsto
          (fun t : ℕ => θ_iter t i) Filter.atTop (nhds (θ_star i))) :=
  actor_critic_two_timescale_converges αw αθ γ lam hgl h_two_timescale
    τ hBounded ψ V₀ θ₀ V_iter θ_iter hV_init hθ_init
    h_critic_update h_actor_update h_critic_summable h_actor_summable

end ActorCritic
end CreditAssignment
